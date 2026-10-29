import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255 BstLean.Part264b
theorem lowSplitE0W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (1 / 8000) x := hx

theorem lowSplitE0W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (193409909 / 500000000) (367683783 / 500000000) c := hc

theorem lowSplitE0W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowSplitE0W_hz2 hx hc) (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowSplitE0W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowSplitE0W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowSplitE0W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE0W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowSplitE0W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowSplitE0W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowSplitE0W_hz11 hx hc) (lowSplitE0W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowSplitE0W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowSplitE0W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (626426463027193639 / 1000000000000000000) (313213231540518477 / 500000000000000000) (kdot ((193409909 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (664942413488200861 / 1000000000000000000)) (a := (293403969832330867 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (33247120674410043 / 50000000000000000)) (a := (293403969790042427 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE0W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (37407392899388281 / 250000000000000000) (37407392899388281 / 250000000000000000) (((193409909 / 500000000) : ℝ)^2) := bsq (bpoint ((193409909 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (212592607100611719 / 250000000000000000) (212592607100611719 / 250000000000000000) ((1 : ℝ) - (((193409909 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowSplitE0W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (461077658427093731 / 500000000000000000) (922155316854187463 / 1000000000000000000) (√((1 : ℝ) - (((193409909 / 500000000) : ℝ)^2))) := bsqrt (lowSplitE0W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (146765576975816917 / 500000000000000000) (58706230790326767 / 200000000000000000) ((√((1 : ℝ) - (((193409909 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowSplitE0W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (60578542604640693 / 250000000000000000) (121157085219695217 / 500000000000000000) (((193409909 / 500000000) : ℝ) * (kdot ((193409909 / 500000000)))) := bmul (bpoint ((193409909 / 500000000) : ℝ)) (lowSplitE0W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (267922662185098303 / 500000000000000000) (535845324391024269 / 1000000000000000000) (((√((1 : ℝ) - (((193409909 / 500000000) : ℝ)^2))) / Real.pi) + (((193409909 / 500000000) : ℝ) * (kdot ((193409909 / 500000000))))) := badd (lowSplitE0W_hz18 hx hc) (lowSplitE0W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (267922662185098303 / 500000000000000000) (535845324391024269 / 1000000000000000000) (kappa ((193409909 / 500000000))) := by rw [kappa_eq]; exact (lowSplitE0W_hz20 hx hc)

theorem lowSplitE0W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (4768690419478873 / 6250000000000000) (762990467116619683 / 1000000000000000000) (kdot ((367683783 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (97626069854007487 / 250000000000000000)) (a := (93073425917147017 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (390504279416029947 / 1000000000000000000)) (a := (186146851834294033 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE0W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (135191364281191089 / 250000000000000000) (135191364281191089 / 250000000000000000) (((367683783 / 500000000) : ℝ)^2) := bsq (bpoint ((367683783 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (114808635718808911 / 250000000000000000) (114808635718808911 / 250000000000000000) ((1 : ℝ) - (((367683783 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowSplitE0W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (677668460882779791 / 1000000000000000000) (42354278805173737 / 62500000000000000) (√((1 : ℝ) - (((367683783 / 500000000) : ℝ)^2))) := bsqrt (lowSplitE0W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (53927142663485559 / 250000000000000000) (215708570653942237 / 1000000000000000000) ((√((1 : ℝ) - (((367683783 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowSplitE0W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (140269610671187913 / 250000000000000000) (112215688536950331 / 200000000000000000) (((367683783 / 500000000) : ℝ) * (kdot ((367683783 / 500000000)))) := bmul (bpoint ((367683783 / 500000000) : ℝ)) (lowSplitE0W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (3034324270854273 / 3906250000000000) (194196753334673473 / 250000000000000000) (((√((1 : ℝ) - (((367683783 / 500000000) : ℝ)^2))) / Real.pi) + (((367683783 / 500000000) : ℝ) * (kdot ((367683783 / 500000000))))) := badd (lowSplitE0W_hz26 hx hc) (lowSplitE0W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (3034324270854273 / 3906250000000000) (194196753334673473 / 250000000000000000) (kappa ((367683783 / 500000000))) := by rw [kappa_eq]; exact (lowSplitE0W_hz28 hx hc)

theorem lowSplitE0W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (267922662185098303 / 500000000000000000) (194196753334673473 / 250000000000000000) (kappa c) := bkappa (lowSplitE0W_hz1 hx hc) (by norm_num) (by norm_num) (lowSplitE0W_hz21 hx hc).1 (lowSplitE0W_hz29 hx hc).2

theorem lowSplitE0W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (55803246665326527 / 250000000000000000) (232077337814901697 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowSplitE0W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (55803246665326527 / 125000000000000000) (232077337814901697 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowSplitE0W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowSplitE0W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (55803231040326527 / 125000000000000000) (232077337814901697 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowSplitE0W_hz32 hx hc) (lowSplitE0W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (668151066992048001 / 1000000000000000000) (240872029205811741 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowSplitE0W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowSplitE0W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowSplitE0W_hz36 hx hc) (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (332379951000242683 / 500000000000000000) (240872029205811741 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowSplitE0W_hz35 hx hc) (lowSplitE0W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (332379951000242683 / 500000000000000000) (240872029205811741 / 250000000000000000) (ndm x c) := by
    convert (lowSplitE0W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowSplitE0W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowSplitE0W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE0W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (441905727307694907 / 1000000000000000000) (92830935125960679 / 100000000000000000) ((ndm x c)^2) := bsq (lowSplitE0W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (107169064874039321 / 100000000000000000) (1564882352675430367 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowSplitE0W_hz41 hx hc) (lowSplitE0W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowSplitE0W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE0W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (107169064874039321 / 200000000000000000) (785101351883481399 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowSplitE0W_hz43 hx hc) (lowSplitE0W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (107169064874039321 / 200000000000000000) (785101351883481399 / 1000000000000000000) (nc1 x c) := by
    convert (lowSplitE0W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowSplitE0W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (85000873198863001 / 125000000000000000) (85000873198863603 / 125000000000000000) (kdot ((107169064874039321 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (549740362984668443 / 1000000000000000000)) (a := (502643851633834409 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (274870181492334221 / 500000000000000000)) (a := (251321925816913423 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE0W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (157477836714791517 / 200000000000000000) (196847295893489397 / 250000000000000000) (kdot ((785101351883481399 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (173482393989702859 / 500000000000000000)) (a := (166984144739445747 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (346964787979405717 / 1000000000000000000)) (a := (83492072369722873 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE0W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (85000873198863001 / 125000000000000000) (196847295893489397 / 250000000000000000) (kdot (nc1 x c)) := bkdot (lowSplitE0W_hz47 hx hc) (lowSplitE0W_hz48 hx hc).1 (lowSplitE0W_hz49 hx hc).2

theorem lowSplitE0W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowSplitE0W_hz51 hx hc) (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowSplitE0W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (85000873198863001 / 250000000000000000) (196847295893489397 / 500000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowSplitE0W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (85000873198863001 / 250000000000000000) (98573517681848221 / 250000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowSplitE0W_hz54 hx hc) (lowSplitE0W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (4768690419478873 / 12500000000000000) (190747616779154921 / 500000000000000000) ((kdot ((367683783 / 500000000))) / (2 : ℝ)) := bdiv (lowSplitE0W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (4768690419478873 / 12500000000000000) (95523678124680983 / 250000000000000000) (((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowSplitE0W_hz56 hx hc) (lowSplitE0W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE0W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowSplitE0W_hz58 hx hc) (lowSplitE0W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowSplitE0W_hz3 hx hc) (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE0W_hz60 hx hc) (lowSplitE0W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE0W_hz4 hx hc) (lowSplitE0W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowSplitE0W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowSplitE0W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (617653004168448807 / 1000000000000000000) (618138101477917257 / 1000000000000000000) (√(((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE0W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (617653004168448807 / 1000000000000000000) (314659220682708103 / 500000000000000000) ((√(((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowSplitE0W_hz65 hx hc) (lowSplitE0W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (617653004168448807 / 1000000000000000000) (315258699623122193 / 500000000000000000) (((√(((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE0W_hz66 hx hc) (lowSplitE0W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (13648332114617283 / 15625000000000000) (891686257326250309 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE0W_hz4 hx hc) (lowSplitE0W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (13648332114617283 / 15625000000000000) (891686257326250309 / 1000000000000000000) (neb x (kdot (367683783 / 500000000)/2+√23*x)) := by
    convert (lowSplitE0W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowSplitE0W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowSplitE0W_hz4 hx hc) (lowSplitE0W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowSplitE0W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowSplitE0W_hz3 hx hc) (lowSplitE0W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowSplitE0W_hz71 hx hc) (lowSplitE0W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowSplitE0W_hz4 hx hc) (lowSplitE0W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowSplitE0W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowSplitE0W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowSplitE0W_hz4 hx hc) (lowSplitE0W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowSplitE0W_hz76 hx hc) (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowSplitE0W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowSplitE0W_hz4 hx hc) (lowSplitE0W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowSplitE0W_hz79 hx hc) (lowSplitE0W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowSplitE0W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowSplitE0W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowSplitE0W_hz70 hx hc) (lowSplitE0W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowSplitE0W_hz82 hx hc) (lowSplitE0W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowSplitE0W_hz4 hx hc) (lowSplitE0W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowSplitE0W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowSplitE0W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (145774546131057291 / 250000000000000000) (627928396178571371 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE0W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (145774546131057291 / 125000000000000000) (627928396178571371 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowSplitE0W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE0W_hz70 hx hc) (lowSplitE0W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (5340639698149189 / 250000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE0W_hz87 hx hc) (lowSplitE0W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowSplitE0W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (10825955334908507 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowSplitE0W_hz89 hx hc) (lowSplitE0W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (10825955334908507 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowSplitE0W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (10825955334908507 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowSplitE0W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowSplitE0W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowSplitE0W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowSplitE0W_hz94 hx hc) (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowSplitE0W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowSplitE0W_hz96 hx hc) (lowSplitE0W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowSplitE0W_hz97 hx hc) (lowSplitE0W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowSplitE0W_hz98 hx hc) (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowSplitE0W_hz95 hx hc) (lowSplitE0W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowSplitE0W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (11221539827840119 / 250000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowSplitE0W_hz93 hx hc) (lowSplitE0W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (584538674667561 / 12500000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowSplitE0W_hz100 hx hc) (lowSplitE0W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (85000873198863001 / 125000000000000000) (98573517681848221 / 125000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowSplitE0W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (190747616779154919 / 250000000000000000) (795104381504495883 / 1000000000000000000) ((neb x (kdot (367683783 / 500000000)/2+√23*x))^2) := bsq (lowSplitE0W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowSplitE0W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowSplitE0W_hz106 hx hc) (lowSplitE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (190747616779154919 / 250000000000000000) (795419691516368013 / 1000000000000000000) (((neb x (kdot (367683783 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowSplitE0W_hz105 hx hc) (lowSplitE0W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (259419423789284157 / 500000000000000000) (313629268104715839 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (367683783 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowSplitE0W_hz104 hx hc) (lowSplitE0W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (259419423789284157 / 500000000000000000) (337010815091418279 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (367683783 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowSplitE0W_hz103 hx hc) (lowSplitE0W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) : B (259419423789284157 / 500000000000000000) (337010815091418279 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (367683783 / 500000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowSplitE0W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowSplitE0W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193409909 / 500000000) (367683783 / 500000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (367683783 / 500000000)/2+√23*x)^2) (np1 x) ≤ (674021631 / 1000000000) :=
  (lowSplitE0W_hz111 hx hc).2.trans (by norm_num)

theorem lowSplitE0C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (1 / 8000) x := hx

theorem lowSplitE0C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (57745557 / 125000000) (125645833 / 200000000) c := hc

theorem lowSplitE0C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowSplitE0C_hz2 hx hc) (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowSplitE0C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowSplitE0C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowSplitE0C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE0C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowSplitE0C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowSplitE0C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowSplitE0C_hz11 hx hc) (lowSplitE0C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowSplitE0C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowSplitE0C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (652855239333013439 / 1000000000000000000) (81606904916701763 / 125000000000000000) (kdot ((57745557 / 125000000))) := by
    constructor
    · apply bkdot_lower (q := (606648428095991609 / 1000000000000000000)) (a := (109058742984359199 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (75831053511998951 / 125000000000000000)) (a := (21811748596834099 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE0C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (3334549353240249 / 15625000000000000) (3334549353240249 / 15625000000000000) (((57745557 / 125000000) : ℝ)^2) := bsq (bpoint ((57745557 / 125000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (12290450646759751 / 15625000000000000) (12290450646759751 / 15625000000000000) ((1 : ℝ) - (((57745557 / 125000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowSplitE0C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (886898439164611487 / 1000000000000000000) (27715576223894109 / 31250000000000000) (√((1 : ℝ) - (((57745557 / 125000000) : ℝ)^2))) := bsqrt (lowSplitE0C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (282308541227069077 / 1000000000000000000) (141154270613534539 / 500000000000000000) ((√((1 : ℝ) - (((57745557 / 125000000) : ℝ)^2))) / Real.pi) := bdiv (lowSplitE0C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (75398978871306339 / 250000000000000000) (301595915485502843 / 1000000000000000000) (((57745557 / 125000000) : ℝ) * (kdot ((57745557 / 125000000)))) := bmul (bpoint ((57745557 / 125000000) : ℝ)) (lowSplitE0C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (583904456712294433 / 1000000000000000000) (583904456712571921 / 1000000000000000000) (((√((1 : ℝ) - (((57745557 / 125000000) : ℝ)^2))) / Real.pi) + (((57745557 / 125000000) : ℝ) * (kdot ((57745557 / 125000000))))) := badd (lowSplitE0C_hz18 hx hc) (lowSplitE0C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (583904456712294433 / 1000000000000000000) (583904456712571921 / 1000000000000000000) (kappa ((57745557 / 125000000))) := by rw [kappa_eq]; exact (lowSplitE0C_hz20 hx hc)

theorem lowSplitE0C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (89527495865508537 / 125000000000000000) (716219966924068303 / 1000000000000000000) (kdot ((125645833 / 200000000))) := by
    constructor
    · apply bkdot_lower (q := (119459282598116467 / 250000000000000000)) (a := (111440158393351947 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (477837130392465867 / 1000000000000000000)) (a := (222880316786703889 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE0C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (15786875350263889 / 40000000000000000) (15786875350263889 / 40000000000000000) (((125645833 / 200000000) : ℝ)^2) := bsq (bpoint ((125645833 / 200000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (24213124649736111 / 40000000000000000) (24213124649736111 / 40000000000000000) ((1 : ℝ) - (((125645833 / 200000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowSplitE0C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (778028351824920821 / 1000000000000000000) (389014175912460411 / 500000000000000000) (√((1 : ℝ) - (((125645833 / 200000000) : ℝ)^2))) := bsqrt (lowSplitE0C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (247654116117152791 / 1000000000000000000) (247654116117152793 / 1000000000000000000) ((√((1 : ℝ) - (((125645833 / 200000000) : ℝ)^2))) / Real.pi) := bdiv (lowSplitE0C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (449950271777035043 / 1000000000000000000) (449950271777035049 / 1000000000000000000) (((125645833 / 200000000) : ℝ) * (kdot ((125645833 / 200000000)))) := bmul (bpoint ((125645833 / 200000000) : ℝ)) (lowSplitE0C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (348802193947093917 / 500000000000000000) (348802193947093921 / 500000000000000000) (((√((1 : ℝ) - (((125645833 / 200000000) : ℝ)^2))) / Real.pi) + (((125645833 / 200000000) : ℝ) * (kdot ((125645833 / 200000000))))) := badd (lowSplitE0C_hz26 hx hc) (lowSplitE0C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (348802193947093917 / 500000000000000000) (348802193947093921 / 500000000000000000) (kappa ((125645833 / 200000000))) := by rw [kappa_eq]; exact (lowSplitE0C_hz28 hx hc)

theorem lowSplitE0C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (583904456712294433 / 1000000000000000000) (348802193947093921 / 500000000000000000) (kappa c) := bkappa (lowSplitE0C_hz1 hx hc) (by norm_num) (by norm_num) (lowSplitE0C_hz21 hx hc).1 (lowSplitE0C_hz29 hx hc).2

theorem lowSplitE0C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (151197806052906079 / 500000000000000000) (416095543287705567 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowSplitE0C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (151197806052906079 / 250000000000000000) (416095543287705567 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowSplitE0C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowSplitE0C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (151197774802906079 / 250000000000000000) (416095543287705567 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowSplitE0C_hz32 hx hc) (lowSplitE0C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (194420790299614099 / 250000000000000000) (36489803212961533 / 40000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowSplitE0C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowSplitE0C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowSplitE0C_hz36 hx hc) (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (774291996206893761 / 1000000000000000000) (36489803212961533 / 40000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowSplitE0C_hz35 hx hc) (lowSplitE0C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (774291996206893761 / 1000000000000000000) (36489803212961533 / 40000000000000000) (ndm x c) := by
    convert (lowSplitE0C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowSplitE0C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowSplitE0C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE0C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (299764047695028191 / 500000000000000000) (13002985727740799 / 15625000000000000) ((ndm x c)^2) := bsq (lowSplitE0C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (18247014272259201 / 15625000000000000) (351814996148267223 / 250000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowSplitE0C_hz41 hx hc) (lowSplitE0C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowSplitE0C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE0C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (18247014272259201 / 31250000000000000) (706022222352135481 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowSplitE0C_hz43 hx hc) (lowSplitE0C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (18247014272259201 / 31250000000000000) (706022222352135481 / 1000000000000000000) (nc1 x c) := by
    convert (lowSplitE0C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowSplitE0C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (69847573639397623 / 100000000000000000) (174618934098494097 / 250000000000000000) (kdot ((18247014272259201 / 31250000000000000))) := by
    constructor
    · apply bkdot_lower (q := (512545047749914027 / 1000000000000000000)) (a := (236816602855939133 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (256272523874957013 / 500000000000000000)) (a := (23681660285593901 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE0C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (187378037661628153 / 250000000000000000) (374756075323256307 / 500000000000000000) (kdot ((706022222352135481 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (83022327586823681 / 200000000000000000)) (a := (24591587104450713 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (103777909483529601 / 250000000000000000)) (a := (196732696835605703 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE0C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (69847573639397623 / 100000000000000000) (374756075323256307 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowSplitE0C_hz47 hx hc) (lowSplitE0C_hz48 hx hc).1 (lowSplitE0C_hz49 hx hc).2

theorem lowSplitE0C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowSplitE0C_hz51 hx hc) (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowSplitE0C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (69847573639397623 / 200000000000000000) (374756075323256307 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowSplitE0C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (69847573639397623 / 200000000000000000) (375355554263670397 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowSplitE0C_hz54 hx hc) (lowSplitE0C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (89527495865508537 / 250000000000000000) (44763747932754269 / 125000000000000000) ((kdot ((125645833 / 200000000))) / (2 : ℝ)) := bdiv (lowSplitE0C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (89527495865508537 / 250000000000000000) (179354731201224121 / 500000000000000000) (((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowSplitE0C_hz56 hx hc) (lowSplitE0C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE0C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowSplitE0C_hz58 hx hc) (lowSplitE0C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowSplitE0C_hz3 hx hc) (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE0C_hz60 hx hc) (lowSplitE0C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE0C_hz4 hx hc) (lowSplitE0C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowSplitE0C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowSplitE0C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (59842291355030361 / 100000000000000000) (299461793223462917 / 500000000000000000) (√(((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE0C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (59842291355030361 / 100000000000000000) (610103926334424783 / 1000000000000000000) ((√(((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowSplitE0C_hz65 hx hc) (lowSplitE0C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (59842291355030361 / 100000000000000000) (611302884215252963 / 1000000000000000000) (((√(((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE0C_hz66 hx hc) (lowSplitE0C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (21157445009441539 / 25000000000000000) (216128207393750137 / 250000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE0C_hz4 hx hc) (lowSplitE0C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (21157445009441539 / 25000000000000000) (216128207393750137 / 250000000000000000) (neb x (kdot (125645833 / 200000000)/2+√23*x)) := by
    convert (lowSplitE0C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowSplitE0C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowSplitE0C_hz4 hx hc) (lowSplitE0C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowSplitE0C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowSplitE0C_hz3 hx hc) (lowSplitE0C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowSplitE0C_hz71 hx hc) (lowSplitE0C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowSplitE0C_hz4 hx hc) (lowSplitE0C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowSplitE0C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowSplitE0C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowSplitE0C_hz4 hx hc) (lowSplitE0C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowSplitE0C_hz76 hx hc) (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowSplitE0C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowSplitE0C_hz4 hx hc) (lowSplitE0C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowSplitE0C_hz79 hx hc) (lowSplitE0C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowSplitE0C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowSplitE0C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowSplitE0C_hz70 hx hc) (lowSplitE0C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowSplitE0C_hz82 hx hc) (lowSplitE0C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowSplitE0C_hz4 hx hc) (lowSplitE0C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowSplitE0C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowSplitE0C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (118192701669263507 / 200000000000000000) (76582834469415207 / 125000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE0C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (118192701669263507 / 100000000000000000) (76582834469415207 / 62500000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowSplitE0C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE0C_hz70 hx hc) (lowSplitE0C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (10421604207186309 / 500000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE0C_hz87 hx hc) (lowSplitE0C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowSplitE0C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (5283140072898219 / 250000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowSplitE0C_hz89 hx hc) (lowSplitE0C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (5283140072898219 / 125000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowSplitE0C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (5283140072898219 / 125000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowSplitE0C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowSplitE0C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowSplitE0C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowSplitE0C_hz94 hx hc) (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowSplitE0C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowSplitE0C_hz96 hx hc) (lowSplitE0C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowSplitE0C_hz97 hx hc) (lowSplitE0C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowSplitE0C_hz98 hx hc) (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowSplitE0C_hz95 hx hc) (lowSplitE0C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowSplitE0C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (21904752018667569 / 500000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowSplitE0C_hz93 hx hc) (lowSplitE0C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (22843219349689771 / 500000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowSplitE0C_hz100 hx hc) (lowSplitE0C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (69847573639397623 / 100000000000000000) (375355554263670397 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowSplitE0C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (358109983462034147 / 500000000000000000) (747382432499773943 / 1000000000000000000) ((neb x (kdot (125645833 / 200000000)/2+√23*x))^2) := bsq (lowSplitE0C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowSplitE0C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowSplitE0C_hz106 hx hc) (lowSplitE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (358109983462034147 / 500000000000000000) (747697742511646073 / 1000000000000000000) (((neb x (kdot (125645833 / 200000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowSplitE0C_hz105 hx hc) (lowSplitE0C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (5002622688173579 / 10000000000000000) (35081562570269253 / 62500000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (125645833 / 200000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowSplitE0C_hz104 hx hc) (lowSplitE0C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (5002622688173579 / 10000000000000000) (60699143982368759 / 100000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (125645833 / 200000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowSplitE0C_hz103 hx hc) (lowSplitE0C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE0C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) : B (5002622688173579 / 10000000000000000) (60699143982368759 / 100000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (125645833 / 200000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowSplitE0C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowSplitE0C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57745557 / 125000000) (125645833 / 200000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (125645833 / 200000000)/2+√23*x)^2) (np1 x) ≤ (7587393 / 12500000) :=
  (lowSplitE0C_hz111 hx hc).2.trans (by norm_num)

theorem lowSplitE1W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowSplitE1W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (193153297 / 500000000) (734911287 / 1000000000) c := hc

theorem lowSplitE1W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowSplitE1W_hz2 hx hc) (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowSplitE1W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowSplitE1W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowSplitE1W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE1W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowSplitE1W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowSplitE1W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowSplitE1W_hz11 hx hc) (lowSplitE1W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowSplitE1W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowSplitE1W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (626249328856999519 / 1000000000000000000) (78281166114057317 / 125000000000000000) (kdot ((193153297 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (133068750716717101 / 200000000000000000)) (a := (14677154534213813 / 25000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (20791992299487047 / 31250000000000000)) (a := (587086181281437701 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE1W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (37308196141970209 / 250000000000000000) (37308196141970209 / 250000000000000000) (((193153297 / 500000000) : ℝ)^2) := bsq (bpoint ((193153297 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (212691803858029791 / 250000000000000000) (212691803858029791 / 250000000000000000) ((1 : ℝ) - (((193153297 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowSplitE1W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (461185216434817857 / 500000000000000000) (184474086573927143 / 200000000000000000) (√((1 : ℝ) - (((193153297 / 500000000) : ℝ)^2))) := bsqrt (lowSplitE1W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (146799813753013739 / 500000000000000000) (293599627506027479 / 1000000000000000000) ((√((1 : ℝ) - (((193153297 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowSplitE1W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (241924245225533397 / 1000000000000000000) (120962122623478791 / 500000000000000000) (((193153297 / 500000000) : ℝ) * (kdot ((193153297 / 500000000)))) := bmul (bpoint ((193153297 / 500000000) : ℝ)) (lowSplitE1W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (4284190981852487 / 8000000000000000) (535523872752985061 / 1000000000000000000) (((√((1 : ℝ) - (((193153297 / 500000000) : ℝ)^2))) / Real.pi) + (((193153297 / 500000000) : ℝ) * (kdot ((193153297 / 500000000))))) := badd (lowSplitE1W_hz18 hx hc) (lowSplitE1W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (4284190981852487 / 8000000000000000) (535523872752985061 / 1000000000000000000) (kappa ((193153297 / 500000000))) := by rw [kappa_eq]; exact (lowSplitE1W_hz20 hx hc)

theorem lowSplitE1W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (38138811251268967 / 50000000000000000) (381388112512689671 / 500000000000000000) (kdot ((734911287 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (195446089935519583 / 500000000000000000)) (a := (93157558589638313 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (78178435974207833 / 200000000000000000)) (a := (1490520937434213 / 4000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE1W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (540094599759996369 / 1000000000000000000) (540094599759996369 / 1000000000000000000) (((734911287 / 1000000000) : ℝ)^2) := bsq (bpoint ((734911287 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (459905400240003631 / 1000000000000000000) (459905400240003631 / 1000000000000000000) ((1 : ℝ) - (((734911287 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowSplitE1W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (678163254858300053 / 1000000000000000000) (339081627429150027 / 500000000000000000) (√((1 : ℝ) - (((734911287 / 1000000000) : ℝ)^2))) := bsqrt (lowSplitE1W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (53966517116993629 / 250000000000000000) (215866068467974517 / 1000000000000000000) ((√((1 : ℝ) - (((734911287 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowSplitE1W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (280286428613201569 / 500000000000000000) (28028642861320157 / 50000000000000000) (((734911287 / 1000000000) : ℝ) * (kdot ((734911287 / 1000000000)))) := bmul (bpoint ((734911287 / 1000000000) : ℝ)) (lowSplitE1W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (388219462847188827 / 500000000000000000) (776438925694377657 / 1000000000000000000) (((√((1 : ℝ) - (((734911287 / 1000000000) : ℝ)^2))) / Real.pi) + (((734911287 / 1000000000) : ℝ) * (kdot ((734911287 / 1000000000))))) := badd (lowSplitE1W_hz26 hx hc) (lowSplitE1W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (388219462847188827 / 500000000000000000) (776438925694377657 / 1000000000000000000) (kappa ((734911287 / 1000000000))) := by rw [kappa_eq]; exact (lowSplitE1W_hz28 hx hc)

theorem lowSplitE1W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (4284190981852487 / 8000000000000000) (776438925694377657 / 1000000000000000000) (kappa c) := bkappa (lowSplitE1W_hz1 hx hc) (by norm_num) (by norm_num) (lowSplitE1W_hz21 hx hc).1 (lowSplitE1W_hz29 hx hc).2

theorem lowSplitE1W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (223561074305622343 / 1000000000000000000) (3715809018147513 / 8000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowSplitE1W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (223561074305622343 / 500000000000000000) (3715809018147513 / 4000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowSplitE1W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowSplitE1W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (223561011805622343 / 500000000000000000) (3715809018147513 / 4000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowSplitE1W_hz32 hx hc) (lowSplitE1W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (13373436710303671 / 20000000000000000) (481910846147105889 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowSplitE1W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowSplitE1W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowSplitE1W_hz36 hx hc) (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (133056134104724183 / 200000000000000000) (481910846147105889 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowSplitE1W_hz35 hx hc) (lowSplitE1W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (133056134104724183 / 200000000000000000) (481910846147105889 / 500000000000000000) (ndm x c) := by
    convert (lowSplitE1W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowSplitE1W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowSplitE1W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE1W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (221299185286179323 / 500000000000000000) (232238063634219563 / 250000000000000000) ((ndm x c)^2) := bsq (lowSplitE1W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (267761936365780437 / 250000000000000000) (391047427352691657 / 250000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowSplitE1W_hz41 hx hc) (lowSplitE1W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowSplitE1W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE1W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (267761936365780437 / 500000000000000000) (784753852812684939 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowSplitE1W_hz43 hx hc) (lowSplitE1W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (267761936365780437 / 500000000000000000) (784753852812684939 / 1000000000000000000) (nc1 x c) := by
    convert (lowSplitE1W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowSplitE1W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (679885811933095093 / 1000000000000000000) (42492863245818751 / 62500000000000000) (kdot ((267761936365780437 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (274994125651612313 / 500000000000000000)) (a := (100566838154084991 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (4399906010425797 / 8000000000000000)) (a := (62854273846302153 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE1W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (78721065770037063 / 100000000000000000) (787210657700370633 / 1000000000000000000) (kdot ((784753852812684939 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (347279005523862403 / 1000000000000000000)) (a := (334248717265359733 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (173639502761931201 / 500000000000000000)) (a := (334248717265359731 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE1W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (679885811933095093 / 1000000000000000000) (787210657700370633 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowSplitE1W_hz47 hx hc) (lowSplitE1W_hz48 hx hc).1 (lowSplitE1W_hz49 hx hc).2

theorem lowSplitE1W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowSplitE1W_hz51 hx hc) (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowSplitE1W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (169971452983273773 / 500000000000000000) (393605328850185317 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowSplitE1W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (169971452983273773 / 500000000000000000) (394204807790599407 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowSplitE1W_hz54 hx hc) (lowSplitE1W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (38138811251268967 / 100000000000000000) (381388112512689671 / 1000000000000000000) ((kdot ((734911287 / 1000000000))) / (2 : ℝ)) := bdiv (lowSplitE1W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (38138811251268967 / 100000000000000000) (381987591453103761 / 1000000000000000000) (((kdot ((734911287 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowSplitE1W_hz56 hx hc) (lowSplitE1W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE1W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowSplitE1W_hz58 hx hc) (lowSplitE1W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowSplitE1W_hz3 hx hc) (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE1W_hz60 hx hc) (lowSplitE1W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE1W_hz4 hx hc) (lowSplitE1W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowSplitE1W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowSplitE1W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (617566281878058551 / 1000000000000000000) (61805144725427491 / 100000000000000000) (√(((kdot ((734911287 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE1W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (617566281878058551 / 1000000000000000000) (629231787141773859 / 1000000000000000000) ((√(((kdot ((734911287 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowSplitE1W_hz65 hx hc) (lowSplitE1W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (617566281878058551 / 1000000000000000000) (630430745022602039 / 1000000000000000000) (((√(((kdot ((734911287 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE1W_hz66 hx hc) (lowSplitE1W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (436685305748138077 / 500000000000000000) (89156370974793839 / 100000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((734911287 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE1W_hz4 hx hc) (lowSplitE1W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (436685305748138077 / 500000000000000000) (89156370974793839 / 100000000000000000) (neb x (kdot (734911287 / 1000000000)/2+√23*x)) := by
    convert (lowSplitE1W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowSplitE1W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowSplitE1W_hz4 hx hc) (lowSplitE1W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowSplitE1W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowSplitE1W_hz3 hx hc) (lowSplitE1W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowSplitE1W_hz71 hx hc) (lowSplitE1W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowSplitE1W_hz4 hx hc) (lowSplitE1W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowSplitE1W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowSplitE1W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowSplitE1W_hz4 hx hc) (lowSplitE1W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowSplitE1W_hz76 hx hc) (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowSplitE1W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowSplitE1W_hz4 hx hc) (lowSplitE1W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowSplitE1W_hz79 hx hc) (lowSplitE1W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowSplitE1W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowSplitE1W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowSplitE1W_hz70 hx hc) (lowSplitE1W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowSplitE1W_hz82 hx hc) (lowSplitE1W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowSplitE1W_hz4 hx hc) (lowSplitE1W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowSplitE1W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowSplitE1W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (583046229699281689 / 1000000000000000000) (156964328708507727 / 250000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE1W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (583046229699281689 / 500000000000000000) (156964328708507727 / 125000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowSplitE1W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE1W_hz70 hx hc) (lowSplitE1W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (5340035139010343 / 250000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE1W_hz87 hx hc) (lowSplitE1W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowSplitE1W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (2164949243326163 / 100000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowSplitE1W_hz89 hx hc) (lowSplitE1W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (2164949243326163 / 50000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowSplitE1W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (2164949243326163 / 50000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowSplitE1W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowSplitE1W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowSplitE1W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowSplitE1W_hz94 hx hc) (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowSplitE1W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowSplitE1W_hz96 hx hc) (lowSplitE1W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowSplitE1W_hz97 hx hc) (lowSplitE1W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowSplitE1W_hz98 hx hc) (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowSplitE1W_hz95 hx hc) (lowSplitE1W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowSplitE1W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (22440573055848639 / 500000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowSplitE1W_hz93 hx hc) (lowSplitE1W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (23379040386870841 / 500000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowSplitE1W_hz100 hx hc) (lowSplitE1W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (169971452983273773 / 250000000000000000) (394204807790599407 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowSplitE1W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (95347028128172417 / 125000000000000000) (198721462134876533 / 250000000000000000) ((neb x (kdot (734911287 / 1000000000)/2+√23*x))^2) := bsq (lowSplitE1W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowSplitE1W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowSplitE1W_hz106 hx hc) (lowSplitE1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (95347028128172417 / 125000000000000000) (397600579275689131 / 500000000000000000) (((neb x (kdot (734911287 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowSplitE1W_hz105 hx hc) (lowSplitE1W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (518600733074641277 / 1000000000000000000) (9796003745675251 / 15625000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (734911287 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowSplitE1W_hz104 hx hc) (lowSplitE1W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (518600733074641277 / 1000000000000000000) (336851160248478873 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (734911287 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowSplitE1W_hz103 hx hc) (lowSplitE1W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) : B (518600733074641277 / 1000000000000000000) (336851160248478873 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (734911287 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowSplitE1W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowSplitE1W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (734911287 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (734911287 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (673702321 / 1000000000) :=
  (lowSplitE1W_hz111 hx hc).2.trans (by norm_num)

theorem lowSplitE1C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (1 / 8000) x := hx

theorem lowSplitE1C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (461458779 / 1000000000) (39233919 / 62500000) c := hc

theorem lowSplitE1C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowSplitE1C_hz2 hx hc) (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowSplitE1C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowSplitE1C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowSplitE1C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE1C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowSplitE1C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowSplitE1C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowSplitE1C_hz11 hx hc) (lowSplitE1C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowSplitE1C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowSplitE1C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (652673777628489537 / 1000000000000000000) (652673777629109419 / 1000000000000000000) (kdot ((461458779 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (607038435777271381 / 1000000000000000000)) (a := (545578754300716081 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (30351921788863569 / 50000000000000000)) (a := (4364630034397939 / 8000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE1C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (212944204716170841 / 1000000000000000000) (212944204716170841 / 1000000000000000000) (((461458779 / 1000000000) : ℝ)^2) := bsq (bpoint ((461458779 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (787055795283829159 / 1000000000000000000) (787055795283829159 / 1000000000000000000) ((1 : ℝ) - (((461458779 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowSplitE1C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (887161651157120947 / 1000000000000000000) (221790412789280237 / 250000000000000000) (√((1 : ℝ) - (((461458779 / 1000000000) : ℝ)^2))) := bsqrt (lowSplitE1C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (70598081051611743 / 250000000000000000) (282392324206446973 / 1000000000000000000) ((√((1 : ℝ) - (((461458779 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowSplitE1C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (301182044509760297 / 1000000000000000000) (75295511127511587 / 250000000000000000) (((461458779 / 1000000000) : ℝ) * (kdot ((461458779 / 1000000000)))) := bmul (bpoint ((461458779 / 1000000000) : ℝ)) (lowSplitE1C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (583574368716207269 / 1000000000000000000) (583574368716493321 / 1000000000000000000) (((√((1 : ℝ) - (((461458779 / 1000000000) : ℝ)^2))) / Real.pi) + (((461458779 / 1000000000) : ℝ) * (kdot ((461458779 / 1000000000))))) := badd (lowSplitE1C_hz18 hx hc) (lowSplitE1C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (583574368716207269 / 1000000000000000000) (583574368716493321 / 1000000000000000000) (kappa ((461458779 / 1000000000))) := by rw [kappa_eq]; exact (lowSplitE1C_hz20 hx hc)

theorem lowSplitE1C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (716020994371229649 / 1000000000000000000) (89502624296403707 / 125000000000000000) (kdot ((39233919 / 62500000))) := by
    constructor
    · apply bkdot_lower (q := (119555274015151589 / 250000000000000000)) (a := (223036589464269869 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (95644219212121271 / 200000000000000000)) (a := (27879573683033733 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE1C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (1539300400098561 / 3906250000000000) (1539300400098561 / 3906250000000000) (((39233919 / 62500000) : ℝ)^2) := bsq (bpoint ((39233919 / 62500000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (2366949599901439 / 3906250000000000) (2366949599901439 / 3906250000000000) ((1 : ℝ) - (((39233919 / 62500000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowSplitE1C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (778420900011535137 / 1000000000000000000) (389210450005767569 / 500000000000000000) (√((1 : ℝ) - (((39233919 / 62500000) : ℝ)^2))) := bsqrt (lowSplitE1C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (967886984709983 / 3906250000000000) (247779068085755649 / 1000000000000000000) ((√((1 : ℝ) - (((39233919 / 62500000) : ℝ)^2))) / Real.pi) := bdiv (lowSplitE1C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (449476955127364479 / 1000000000000000000) (89895391025472897 / 200000000000000000) (((39233919 / 62500000) : ℝ) * (kdot ((39233919 / 62500000)))) := bmul (bpoint ((39233919 / 62500000) : ℝ)) (lowSplitE1C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (697256023213120127 / 1000000000000000000) (348628011606560067 / 500000000000000000) (((√((1 : ℝ) - (((39233919 / 62500000) : ℝ)^2))) / Real.pi) + (((39233919 / 62500000) : ℝ) * (kdot ((39233919 / 62500000))))) := badd (lowSplitE1C_hz26 hx hc) (lowSplitE1C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (697256023213120127 / 1000000000000000000) (348628011606560067 / 500000000000000000) (kappa ((39233919 / 62500000))) := by rw [kappa_eq]; exact (lowSplitE1C_hz28 hx hc)

theorem lowSplitE1C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (583574368716207269 / 1000000000000000000) (348628011606560067 / 500000000000000000) (kappa c) := bkappa (lowSplitE1C_hz1 hx hc) (by norm_num) (by norm_num) (lowSplitE1C_hz21 hx hc).1 (lowSplitE1C_hz29 hx hc).2

theorem lowSplitE1C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (151371988393439933 / 500000000000000000) (416425631283792731 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowSplitE1C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (151371988393439933 / 250000000000000000) (416425631283792731 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowSplitE1C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowSplitE1C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (151371957143439933 / 250000000000000000) (416425631283792731 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowSplitE1C_hz32 hx hc) (lowSplitE1C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (778130984201091771 / 1000000000000000000) (11407585624319689 / 12500000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowSplitE1C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowSplitE1C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowSplitE1C_hz36 hx hc) (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (48421238700595571 / 62500000000000000) (11407585624319689 / 12500000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowSplitE1C_hz35 hx hc) (lowSplitE1C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (48421238700595571 / 62500000000000000) (11407585624319689 / 12500000000000000) (ndm x c) := by
    convert (lowSplitE1C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowSplitE1C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowSplitE1C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE1C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (60022178746881389 / 100000000000000000) (104106407820948183 / 125000000000000000) ((ndm x c)^2) := bsq (lowSplitE1C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (145893592179051817 / 125000000000000000) (175820786564288923 / 125000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowSplitE1C_hz41 hx hc) (lowSplitE1C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowSplitE1C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowSplitE1C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (145893592179051817 / 250000000000000000) (705674197091391589 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowSplitE1C_hz43 hx hc) (lowSplitE1C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (145893592179051817 / 250000000000000000) (705674197091391589 / 1000000000000000000) (nc1 x c) := by
    convert (lowSplitE1C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowSplitE1C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (139669266022521701 / 200000000000000000) (349173165056304333 / 500000000000000000) (kdot ((145893592179051817 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (16025054536581223 / 31250000000000000)) (a := (118459119155828719 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (102560349034119827 / 200000000000000000)) (a := (7403694947239291 / 15625000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE1C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (374677881044794119 / 500000000000000000) (749355762089588241 / 1000000000000000000) (kdot ((705674197091391589 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (415399652504438283 / 1000000000000000000)) (a := (393711048241980969 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (207699826252219141 / 500000000000000000)) (a := (393711048241980967 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowSplitE1C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (139669266022521701 / 200000000000000000) (749355762089588241 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowSplitE1C_hz47 hx hc) (lowSplitE1C_hz48 hx hc).1 (lowSplitE1C_hz49 hx hc).2

theorem lowSplitE1C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowSplitE1C_hz51 hx hc) (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowSplitE1C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (87293291264076063 / 250000000000000000) (374677881044794121 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowSplitE1C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (87293291264076063 / 250000000000000000) (375277359985208211 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowSplitE1C_hz54 hx hc) (lowSplitE1C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (44751312148201853 / 125000000000000000) (89502624296403707 / 250000000000000000) ((kdot ((39233919 / 62500000))) / (2 : ℝ)) := bdiv (lowSplitE1C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (44751312148201853 / 125000000000000000) (179304988063014459 / 500000000000000000) (((kdot ((39233919 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowSplitE1C_hz56 hx hc) (lowSplitE1C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE1C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowSplitE1C_hz58 hx hc) (lowSplitE1C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowSplitE1C_hz3 hx hc) (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE1C_hz60 hx hc) (lowSplitE1C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE1C_hz4 hx hc) (lowSplitE1C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowSplitE1C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowSplitE1C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (598339784057198409 / 1000000000000000000) (598840526455941289 / 1000000000000000000) (√(((kdot ((39233919 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE1C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (598339784057198409 / 1000000000000000000) (305010433171720119 / 500000000000000000) ((√(((kdot ((39233919 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowSplitE1C_hz65 hx hc) (lowSplitE1C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (598339784057198409 / 1000000000000000000) (305609912112134209 / 500000000000000000) (((√(((kdot ((39233919 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE1C_hz66 hx hc) (lowSplitE1C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (105772529690134873 / 125000000000000000) (864395365009259617 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((39233919 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE1C_hz4 hx hc) (lowSplitE1C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (105772529690134873 / 125000000000000000) (864395365009259617 / 1000000000000000000) (neb x (kdot (39233919 / 62500000)/2+√23*x)) := by
    convert (lowSplitE1C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowSplitE1C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowSplitE1C_hz4 hx hc) (lowSplitE1C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowSplitE1C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowSplitE1C_hz3 hx hc) (lowSplitE1C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowSplitE1C_hz71 hx hc) (lowSplitE1C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowSplitE1C_hz4 hx hc) (lowSplitE1C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowSplitE1C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowSplitE1C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowSplitE1C_hz4 hx hc) (lowSplitE1C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowSplitE1C_hz76 hx hc) (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowSplitE1C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowSplitE1C_hz4 hx hc) (lowSplitE1C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowSplitE1C_hz79 hx hc) (lowSplitE1C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowSplitE1C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowSplitE1C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowSplitE1C_hz70 hx hc) (lowSplitE1C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowSplitE1C_hz82 hx hc) (lowSplitE1C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowSplitE1C_hz4 hx hc) (lowSplitE1C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowSplitE1C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowSplitE1C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (590908762040557537 / 1000000000000000000) (612598857316276923 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowSplitE1C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (590908762040557537 / 500000000000000000) (612598857316276923 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowSplitE1C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowSplitE1C_hz70 hx hc) (lowSplitE1C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (20841037266890769 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowSplitE1C_hz87 hx hc) (lowSplitE1C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowSplitE1C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (21130389144111027 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowSplitE1C_hz89 hx hc) (lowSplitE1C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (21130389144111027 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowSplitE1C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (21130389144111027 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowSplitE1C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowSplitE1C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowSplitE1C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowSplitE1C_hz94 hx hc) (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowSplitE1C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowSplitE1C_hz96 hx hc) (lowSplitE1C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowSplitE1C_hz97 hx hc) (lowSplitE1C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowSplitE1C_hz98 hx hc) (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowSplitE1C_hz95 hx hc) (lowSplitE1C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowSplitE1C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (43805003073274973 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowSplitE1C_hz93 hx hc) (lowSplitE1C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (45681937735319377 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowSplitE1C_hz100 hx hc) (lowSplitE1C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (87293291264076063 / 125000000000000000) (375277359985208211 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowSplitE1C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (143204198874245929 / 200000000000000000) (373589673524745583 / 500000000000000000) ((neb x (kdot (39233919 / 62500000)/2+√23*x))^2) := bsq (lowSplitE1C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowSplitE1C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowSplitE1C_hz106 hx hc) (lowSplitE1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (143204198874245929 / 200000000000000000) (23359208033167603 / 31250000000000000) (((neb x (kdot (39233919 / 62500000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowSplitE1C_hz105 hx hc) (lowSplitE1C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (500030633702728933 / 1000000000000000000) (112207128602014797 / 200000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (39233919 / 62500000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowSplitE1C_hz104 hx hc) (lowSplitE1C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (500030633702728933 / 1000000000000000000) (303358790372696681 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (39233919 / 62500000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowSplitE1C_hz103 hx hc) (lowSplitE1C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowSplitE1C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) : B (500030633702728933 / 1000000000000000000) (303358790372696681 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (39233919 / 62500000)/2+√23*x)^2) (np1 x)) := by
    convert (lowSplitE1C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowSplitE1C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (39233919 / 62500000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (39233919 / 62500000)/2+√23*x)^2) (np1 x) ≤ (606717581 / 1000000000) :=
  (lowSplitE1C_hz111 hx hc).2.trans (by norm_num)

end BstLean.BlueprintLow
