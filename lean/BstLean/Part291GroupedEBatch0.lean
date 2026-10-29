import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255 BstLean.Part264b
theorem lowGroupedE0W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE0W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (193153297 / 500000000) (367683783 / 500000000) c := hc

theorem lowGroupedE0W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE0W_hz2 hx hc) (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE0W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE0W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE0W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE0W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE0W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE0W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE0W_hz11 hx hc) (lowGroupedE0W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE0W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE0W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (626249328856999519 / 1000000000000000000) (78281166114057317 / 125000000000000000) (kdot ((193153297 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (133068750716717101 / 200000000000000000)) (a := (14677154534213813 / 25000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (20791992299487047 / 31250000000000000)) (a := (587086181281437701 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE0W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (37308196141970209 / 250000000000000000) (37308196141970209 / 250000000000000000) (((193153297 / 500000000) : ℝ)^2) := bsq (bpoint ((193153297 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (212691803858029791 / 250000000000000000) (212691803858029791 / 250000000000000000) ((1 : ℝ) - (((193153297 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE0W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (461185216434817857 / 500000000000000000) (184474086573927143 / 200000000000000000) (√((1 : ℝ) - (((193153297 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE0W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (146799813753013739 / 500000000000000000) (293599627506027479 / 1000000000000000000) ((√((1 : ℝ) - (((193153297 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE0W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (241924245225533397 / 1000000000000000000) (120962122623478791 / 500000000000000000) (((193153297 / 500000000) : ℝ) * (kdot ((193153297 / 500000000)))) := bmul (bpoint ((193153297 / 500000000) : ℝ)) (lowGroupedE0W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (4284190981852487 / 8000000000000000) (535523872752985061 / 1000000000000000000) (((√((1 : ℝ) - (((193153297 / 500000000) : ℝ)^2))) / Real.pi) + (((193153297 / 500000000) : ℝ) * (kdot ((193153297 / 500000000))))) := badd (lowGroupedE0W_hz18 hx hc) (lowGroupedE0W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (4284190981852487 / 8000000000000000) (535523872752985061 / 1000000000000000000) (kappa ((193153297 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE0W_hz20 hx hc)

theorem lowGroupedE0W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (4768690419478873 / 6250000000000000) (762990467116619683 / 1000000000000000000) (kdot ((367683783 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (97626069854007487 / 250000000000000000)) (a := (93073425917147017 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (390504279416029947 / 1000000000000000000)) (a := (186146851834294033 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE0W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (135191364281191089 / 250000000000000000) (135191364281191089 / 250000000000000000) (((367683783 / 500000000) : ℝ)^2) := bsq (bpoint ((367683783 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (114808635718808911 / 250000000000000000) (114808635718808911 / 250000000000000000) ((1 : ℝ) - (((367683783 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE0W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (677668460882779791 / 1000000000000000000) (42354278805173737 / 62500000000000000) (√((1 : ℝ) - (((367683783 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE0W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (53927142663485559 / 250000000000000000) (215708570653942237 / 1000000000000000000) ((√((1 : ℝ) - (((367683783 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE0W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (140269610671187913 / 250000000000000000) (112215688536950331 / 200000000000000000) (((367683783 / 500000000) : ℝ) * (kdot ((367683783 / 500000000)))) := bmul (bpoint ((367683783 / 500000000) : ℝ)) (lowGroupedE0W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (3034324270854273 / 3906250000000000) (194196753334673473 / 250000000000000000) (((√((1 : ℝ) - (((367683783 / 500000000) : ℝ)^2))) / Real.pi) + (((367683783 / 500000000) : ℝ) * (kdot ((367683783 / 500000000))))) := badd (lowGroupedE0W_hz26 hx hc) (lowGroupedE0W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (3034324270854273 / 3906250000000000) (194196753334673473 / 250000000000000000) (kappa ((367683783 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE0W_hz28 hx hc)

theorem lowGroupedE0W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (4284190981852487 / 8000000000000000) (194196753334673473 / 250000000000000000) (kappa c) := bkappa (lowGroupedE0W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE0W_hz21 hx hc).1 (lowGroupedE0W_hz29 hx hc).2

theorem lowGroupedE0W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (55803246665326527 / 250000000000000000) (3715809018147513 / 8000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE0W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (55803246665326527 / 125000000000000000) (3715809018147513 / 4000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE0W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (55803231040326527 / 125000000000000000) (3715809018147513 / 4000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE0W_hz32 hx hc) (lowGroupedE0W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (668151066992048001 / 1000000000000000000) (481910846147105889 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE0W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE0W_hz36 hx hc) (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (332379951000242683 / 500000000000000000) (481910846147105889 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE0W_hz35 hx hc) (lowGroupedE0W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (332379951000242683 / 500000000000000000) (481910846147105889 / 500000000000000000) (ndm x c) := by
    convert (lowGroupedE0W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE0W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE0W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE0W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (441905727307694907 / 1000000000000000000) (232238063634219563 / 250000000000000000) ((ndm x c)^2) := bsq (lowGroupedE0W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (267761936365780437 / 250000000000000000) (1564882352675430367 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE0W_hz41 hx hc) (lowGroupedE0W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE0W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE0W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (267761936365780437 / 500000000000000000) (785101351883481399 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE0W_hz43 hx hc) (lowGroupedE0W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (267761936365780437 / 500000000000000000) (785101351883481399 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE0W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE0W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (679885811933095093 / 1000000000000000000) (42492863245818751 / 62500000000000000) (kdot ((267761936365780437 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (274994125651612313 / 500000000000000000)) (a := (100566838154084991 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (4399906010425797 / 8000000000000000)) (a := (62854273846302153 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE0W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (157477836714791517 / 200000000000000000) (196847295893489397 / 250000000000000000) (kdot ((785101351883481399 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (173482393989702859 / 500000000000000000)) (a := (166984144739445747 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (346964787979405717 / 1000000000000000000)) (a := (83492072369722873 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE0W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (679885811933095093 / 1000000000000000000) (196847295893489397 / 250000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE0W_hz47 hx hc) (lowGroupedE0W_hz48 hx hc).1 (lowGroupedE0W_hz49 hx hc).2

theorem lowGroupedE0W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE0W_hz51 hx hc) (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE0W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (169971452983273773 / 500000000000000000) (196847295893489397 / 500000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE0W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (169971452983273773 / 500000000000000000) (98573517681848221 / 250000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE0W_hz54 hx hc) (lowGroupedE0W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (4768690419478873 / 12500000000000000) (190747616779154921 / 500000000000000000) ((kdot ((367683783 / 500000000))) / (2 : ℝ)) := bdiv (lowGroupedE0W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (4768690419478873 / 12500000000000000) (95523678124680983 / 250000000000000000) (((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE0W_hz56 hx hc) (lowGroupedE0W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE0W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE0W_hz58 hx hc) (lowGroupedE0W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE0W_hz3 hx hc) (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE0W_hz60 hx hc) (lowGroupedE0W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE0W_hz4 hx hc) (lowGroupedE0W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE0W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE0W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (617653004168448807 / 1000000000000000000) (618138101477917257 / 1000000000000000000) (√(((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE0W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (617653004168448807 / 1000000000000000000) (314659220682708103 / 500000000000000000) ((√(((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE0W_hz65 hx hc) (lowGroupedE0W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (617653004168448807 / 1000000000000000000) (315258699623122193 / 500000000000000000) (((√(((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE0W_hz66 hx hc) (lowGroupedE0W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (13648332114617283 / 15625000000000000) (891686257326250309 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((367683783 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE0W_hz4 hx hc) (lowGroupedE0W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (13648332114617283 / 15625000000000000) (891686257326250309 / 1000000000000000000) (neb x (kdot (367683783 / 500000000)/2+√23*x)) := by
    convert (lowGroupedE0W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE0W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE0W_hz4 hx hc) (lowGroupedE0W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE0W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE0W_hz3 hx hc) (lowGroupedE0W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE0W_hz71 hx hc) (lowGroupedE0W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE0W_hz4 hx hc) (lowGroupedE0W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE0W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE0W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE0W_hz4 hx hc) (lowGroupedE0W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE0W_hz76 hx hc) (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE0W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE0W_hz4 hx hc) (lowGroupedE0W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE0W_hz79 hx hc) (lowGroupedE0W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE0W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE0W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE0W_hz70 hx hc) (lowGroupedE0W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE0W_hz82 hx hc) (lowGroupedE0W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE0W_hz4 hx hc) (lowGroupedE0W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE0W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE0W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (583046229699281689 / 1000000000000000000) (627928396178571371 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE0W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (583046229699281689 / 500000000000000000) (627928396178571371 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE0W_hz70 hx hc) (lowGroupedE0W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (5340639698149189 / 250000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE0W_hz87 hx hc) (lowGroupedE0W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE0W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (10825955334908507 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE0W_hz89 hx hc) (lowGroupedE0W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (10825955334908507 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (10825955334908507 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE0W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE0W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE0W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE0W_hz94 hx hc) (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE0W_hz96 hx hc) (lowGroupedE0W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE0W_hz97 hx hc) (lowGroupedE0W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE0W_hz98 hx hc) (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE0W_hz95 hx hc) (lowGroupedE0W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE0W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (11221539827840119 / 250000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE0W_hz93 hx hc) (lowGroupedE0W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (584538674667561 / 12500000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE0W_hz100 hx hc) (lowGroupedE0W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (169971452983273773 / 250000000000000000) (98573517681848221 / 125000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (190747616779154919 / 250000000000000000) (795104381504495883 / 1000000000000000000) ((neb x (kdot (367683783 / 500000000)/2+√23*x))^2) := bsq (lowGroupedE0W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE0W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE0W_hz106 hx hc) (lowGroupedE0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (190747616779154919 / 250000000000000000) (795419691516368013 / 1000000000000000000) (((neb x (kdot (367683783 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE0W_hz105 hx hc) (lowGroupedE0W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (25937319661639723 / 50000000000000000) (313629268104715839 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (367683783 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE0W_hz104 hx hc) (lowGroupedE0W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (25937319661639723 / 50000000000000000) (337010815091418279 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (367683783 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE0W_hz103 hx hc) (lowGroupedE0W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) : B (25937319661639723 / 50000000000000000) (337010815091418279 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (367683783 / 500000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE0W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE0W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (193153297 / 500000000) (367683783 / 500000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (367683783 / 500000000)/2+√23*x)^2) (np1 x) ≤ (674021631 / 1000000000) :=
  (lowGroupedE0W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE0C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE0C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (461458779 / 1000000000) (125645833 / 200000000) c := hc

theorem lowGroupedE0C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE0C_hz2 hx hc) (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE0C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE0C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE0C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE0C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE0C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE0C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE0C_hz11 hx hc) (lowGroupedE0C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE0C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE0C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (652673777628489537 / 1000000000000000000) (652673777629109419 / 1000000000000000000) (kdot ((461458779 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (607038435777271381 / 1000000000000000000)) (a := (545578754300716081 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (30351921788863569 / 50000000000000000)) (a := (4364630034397939 / 8000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE0C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (212944204716170841 / 1000000000000000000) (212944204716170841 / 1000000000000000000) (((461458779 / 1000000000) : ℝ)^2) := bsq (bpoint ((461458779 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (787055795283829159 / 1000000000000000000) (787055795283829159 / 1000000000000000000) ((1 : ℝ) - (((461458779 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE0C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (887161651157120947 / 1000000000000000000) (221790412789280237 / 250000000000000000) (√((1 : ℝ) - (((461458779 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE0C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (70598081051611743 / 250000000000000000) (282392324206446973 / 1000000000000000000) ((√((1 : ℝ) - (((461458779 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE0C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (301182044509760297 / 1000000000000000000) (75295511127511587 / 250000000000000000) (((461458779 / 1000000000) : ℝ) * (kdot ((461458779 / 1000000000)))) := bmul (bpoint ((461458779 / 1000000000) : ℝ)) (lowGroupedE0C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (583574368716207269 / 1000000000000000000) (583574368716493321 / 1000000000000000000) (((√((1 : ℝ) - (((461458779 / 1000000000) : ℝ)^2))) / Real.pi) + (((461458779 / 1000000000) : ℝ) * (kdot ((461458779 / 1000000000))))) := badd (lowGroupedE0C_hz18 hx hc) (lowGroupedE0C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (583574368716207269 / 1000000000000000000) (583574368716493321 / 1000000000000000000) (kappa ((461458779 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE0C_hz20 hx hc)

theorem lowGroupedE0C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (89527495865508537 / 125000000000000000) (716219966924068303 / 1000000000000000000) (kdot ((125645833 / 200000000))) := by
    constructor
    · apply bkdot_lower (q := (119459282598116467 / 250000000000000000)) (a := (111440158393351947 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (477837130392465867 / 1000000000000000000)) (a := (222880316786703889 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE0C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (15786875350263889 / 40000000000000000) (15786875350263889 / 40000000000000000) (((125645833 / 200000000) : ℝ)^2) := bsq (bpoint ((125645833 / 200000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (24213124649736111 / 40000000000000000) (24213124649736111 / 40000000000000000) ((1 : ℝ) - (((125645833 / 200000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE0C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (778028351824920821 / 1000000000000000000) (389014175912460411 / 500000000000000000) (√((1 : ℝ) - (((125645833 / 200000000) : ℝ)^2))) := bsqrt (lowGroupedE0C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (247654116117152791 / 1000000000000000000) (247654116117152793 / 1000000000000000000) ((√((1 : ℝ) - (((125645833 / 200000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE0C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (449950271777035043 / 1000000000000000000) (449950271777035049 / 1000000000000000000) (((125645833 / 200000000) : ℝ) * (kdot ((125645833 / 200000000)))) := bmul (bpoint ((125645833 / 200000000) : ℝ)) (lowGroupedE0C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (348802193947093917 / 500000000000000000) (348802193947093921 / 500000000000000000) (((√((1 : ℝ) - (((125645833 / 200000000) : ℝ)^2))) / Real.pi) + (((125645833 / 200000000) : ℝ) * (kdot ((125645833 / 200000000))))) := badd (lowGroupedE0C_hz26 hx hc) (lowGroupedE0C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (348802193947093917 / 500000000000000000) (348802193947093921 / 500000000000000000) (kappa ((125645833 / 200000000))) := by rw [kappa_eq]; exact (lowGroupedE0C_hz28 hx hc)

theorem lowGroupedE0C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (583574368716207269 / 1000000000000000000) (348802193947093921 / 500000000000000000) (kappa c) := bkappa (lowGroupedE0C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE0C_hz21 hx hc).1 (lowGroupedE0C_hz29 hx hc).2

theorem lowGroupedE0C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (151197806052906079 / 500000000000000000) (416425631283792731 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE0C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (151197806052906079 / 250000000000000000) (416425631283792731 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE0C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (151197774802906079 / 250000000000000000) (416425631283792731 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE0C_hz32 hx hc) (lowGroupedE0C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (194420790299614099 / 250000000000000000) (11407585624319689 / 12500000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE0C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE0C_hz36 hx hc) (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (774291996206893761 / 1000000000000000000) (11407585624319689 / 12500000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE0C_hz35 hx hc) (lowGroupedE0C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (774291996206893761 / 1000000000000000000) (11407585624319689 / 12500000000000000) (ndm x c) := by
    convert (lowGroupedE0C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE0C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE0C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE0C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (299764047695028191 / 500000000000000000) (104106407820948183 / 125000000000000000) ((ndm x c)^2) := bsq (lowGroupedE0C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (145893592179051817 / 125000000000000000) (351814996148267223 / 250000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE0C_hz41 hx hc) (lowGroupedE0C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE0C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE0C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (145893592179051817 / 250000000000000000) (706022222352135481 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE0C_hz43 hx hc) (lowGroupedE0C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (145893592179051817 / 250000000000000000) (706022222352135481 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE0C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE0C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (139669266022521701 / 200000000000000000) (349173165056304333 / 500000000000000000) (kdot ((145893592179051817 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (16025054536581223 / 31250000000000000)) (a := (118459119155828719 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (102560349034119827 / 200000000000000000)) (a := (7403694947239291 / 15625000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE0C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (187378037661628153 / 250000000000000000) (374756075323256307 / 500000000000000000) (kdot ((706022222352135481 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (83022327586823681 / 200000000000000000)) (a := (24591587104450713 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (103777909483529601 / 250000000000000000)) (a := (196732696835605703 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE0C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (139669266022521701 / 200000000000000000) (374756075323256307 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE0C_hz47 hx hc) (lowGroupedE0C_hz48 hx hc).1 (lowGroupedE0C_hz49 hx hc).2

theorem lowGroupedE0C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE0C_hz51 hx hc) (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE0C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (87293291264076063 / 250000000000000000) (374756075323256307 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE0C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (87293291264076063 / 250000000000000000) (375355554263670397 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE0C_hz54 hx hc) (lowGroupedE0C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (89527495865508537 / 250000000000000000) (44763747932754269 / 125000000000000000) ((kdot ((125645833 / 200000000))) / (2 : ℝ)) := bdiv (lowGroupedE0C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (89527495865508537 / 250000000000000000) (179354731201224121 / 500000000000000000) (((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE0C_hz56 hx hc) (lowGroupedE0C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE0C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE0C_hz58 hx hc) (lowGroupedE0C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE0C_hz3 hx hc) (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE0C_hz60 hx hc) (lowGroupedE0C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE0C_hz4 hx hc) (lowGroupedE0C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE0C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE0C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (59842291355030361 / 100000000000000000) (299461793223462917 / 500000000000000000) (√(((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE0C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (59842291355030361 / 100000000000000000) (610103926334424783 / 1000000000000000000) ((√(((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE0C_hz65 hx hc) (lowGroupedE0C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (59842291355030361 / 100000000000000000) (611302884215252963 / 1000000000000000000) (((√(((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE0C_hz66 hx hc) (lowGroupedE0C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (21157445009441539 / 25000000000000000) (216128207393750137 / 250000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((125645833 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE0C_hz4 hx hc) (lowGroupedE0C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (21157445009441539 / 25000000000000000) (216128207393750137 / 250000000000000000) (neb x (kdot (125645833 / 200000000)/2+√23*x)) := by
    convert (lowGroupedE0C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE0C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE0C_hz4 hx hc) (lowGroupedE0C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE0C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE0C_hz3 hx hc) (lowGroupedE0C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE0C_hz71 hx hc) (lowGroupedE0C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE0C_hz4 hx hc) (lowGroupedE0C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE0C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE0C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE0C_hz4 hx hc) (lowGroupedE0C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE0C_hz76 hx hc) (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE0C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE0C_hz4 hx hc) (lowGroupedE0C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE0C_hz79 hx hc) (lowGroupedE0C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE0C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE0C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE0C_hz70 hx hc) (lowGroupedE0C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE0C_hz82 hx hc) (lowGroupedE0C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE0C_hz4 hx hc) (lowGroupedE0C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE0C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE0C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (590908762040557537 / 1000000000000000000) (76582834469415207 / 125000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE0C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (590908762040557537 / 500000000000000000) (76582834469415207 / 62500000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE0C_hz70 hx hc) (lowGroupedE0C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (10421604207186309 / 500000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE0C_hz87 hx hc) (lowGroupedE0C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE0C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (5283140072898219 / 250000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE0C_hz89 hx hc) (lowGroupedE0C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (5283140072898219 / 125000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (5283140072898219 / 125000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE0C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE0C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE0C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE0C_hz94 hx hc) (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE0C_hz96 hx hc) (lowGroupedE0C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE0C_hz97 hx hc) (lowGroupedE0C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE0C_hz98 hx hc) (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE0C_hz95 hx hc) (lowGroupedE0C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE0C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (21904752018667569 / 500000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE0C_hz93 hx hc) (lowGroupedE0C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (22843219349689771 / 500000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE0C_hz100 hx hc) (lowGroupedE0C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (87293291264076063 / 125000000000000000) (375355554263670397 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE0C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (358109983462034147 / 500000000000000000) (747382432499773943 / 1000000000000000000) ((neb x (kdot (125645833 / 200000000)/2+√23*x))^2) := bsq (lowGroupedE0C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE0C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE0C_hz106 hx hc) (lowGroupedE0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (358109983462034147 / 500000000000000000) (747697742511646073 / 1000000000000000000) (((neb x (kdot (125645833 / 200000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE0C_hz105 hx hc) (lowGroupedE0C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (25008479272739847 / 50000000000000000) (35081562570269253 / 62500000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (125645833 / 200000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE0C_hz104 hx hc) (lowGroupedE0C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (25008479272739847 / 50000000000000000) (60699143982368759 / 100000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (125645833 / 200000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE0C_hz103 hx hc) (lowGroupedE0C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE0C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) : B (25008479272739847 / 50000000000000000) (60699143982368759 / 100000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (125645833 / 200000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE0C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE0C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (461458779 / 1000000000) (125645833 / 200000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (125645833 / 200000000)/2+√23*x)^2) (np1 x) ≤ (7587393 / 12500000) :=
  (lowGroupedE0C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE2W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE2W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (385280557 / 1000000000) (734454819 / 1000000000) c := hc

theorem lowGroupedE2W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE2W_hz2 hx hc) (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE2W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE2W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE2W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE2W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE2W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE2W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE2W_hz11 hx hc) (lowGroupedE2W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE2W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE2W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (78236915753259599 / 125000000000000000) (625895326084910297 / 1000000000000000000) (kdot ((385280557 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (333073138830347493 / 500000000000000000)) (a := (293821123857520467 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (133229255532138997 / 200000000000000000)) (a := (293821123811312741 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE2W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (148441107602230249 / 1000000000000000000) (148441107602230249 / 1000000000000000000) (((385280557 / 1000000000) : ℝ)^2) := bsq (bpoint ((385280557 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (851558892397769751 / 1000000000000000000) (851558892397769751 / 1000000000000000000) ((1 : ℝ) - (((385280557 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE2W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (461399743280642103 / 500000000000000000) (922799486561284207 / 1000000000000000000) (√((1 : ℝ) - (((385280557 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE2W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (73434049884445711 / 250000000000000000) (146868099768891423 / 500000000000000000) ((√((1 : ℝ) - (((385280557 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE2W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (120572649917511731 / 500000000000000000) (241145299857690869 / 1000000000000000000) (((385280557 / 1000000000) : ℝ) * (kdot ((385280557 / 1000000000)))) := bmul (bpoint ((385280557 / 1000000000) : ℝ)) (lowGroupedE2W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (267440749686403153 / 500000000000000000) (106976299879094743 / 200000000000000000) (((√((1 : ℝ) - (((385280557 / 1000000000) : ℝ)^2))) / Real.pi) + (((385280557 / 1000000000) : ℝ) * (kdot ((385280557 / 1000000000))))) := badd (lowGroupedE2W_hz18 hx hc) (lowGroupedE2W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (267440749686403153 / 500000000000000000) (106976299879094743 / 200000000000000000) (kappa ((385280557 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE2W_hz20 hx hc)

theorem lowGroupedE2W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (381281025219154481 / 500000000000000000) (152512410087661793 / 200000000000000000) (kdot ((734454819 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (4891000751557587 / 12500000000000000)) (a := (74593331802643243 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (391280060124606959 / 1000000000000000000)) (a := (372966659013216213 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE2W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (539423881152322761 / 1000000000000000000) (539423881152322761 / 1000000000000000000) (((734454819 / 1000000000) : ℝ)^2) := bsq (bpoint ((734454819 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (460576118847677239 / 1000000000000000000) (460576118847677239 / 1000000000000000000) ((1 : ℝ) - (((734454819 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE2W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (678657585861734281 / 1000000000000000000) (339328792930867141 / 500000000000000000) (√((1 : ℝ) - (((734454819 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE2W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (1687682960261053 / 7812500000000000) (43204683782682957 / 200000000000000000) ((√((1 : ℝ) - (((734454819 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE2W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (560067372730937079 / 1000000000000000000) (280033686365468541 / 500000000000000000) (((734454819 / 1000000000) : ℝ) * (kdot ((734454819 / 1000000000)))) := bmul (bpoint ((734454819 / 1000000000) : ℝ)) (lowGroupedE2W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (776090791644351863 / 1000000000000000000) (776090791644351867 / 1000000000000000000) (((√((1 : ℝ) - (((734454819 / 1000000000) : ℝ)^2))) / Real.pi) + (((734454819 / 1000000000) : ℝ) * (kdot ((734454819 / 1000000000))))) := badd (lowGroupedE2W_hz26 hx hc) (lowGroupedE2W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (776090791644351863 / 1000000000000000000) (776090791644351867 / 1000000000000000000) (kappa ((734454819 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE2W_hz28 hx hc)

theorem lowGroupedE2W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (267440749686403153 / 500000000000000000) (776090791644351867 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE2W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE2W_hz21 hx hc).1 (lowGroupedE2W_hz29 hx hc).2

theorem lowGroupedE2W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (223909208355648133 / 1000000000000000000) (232559250313596847 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE2W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (223909208355648133 / 500000000000000000) (232559250313596847 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE2W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (223909145855648133 / 500000000000000000) (232559250313596847 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE2W_hz32 hx hc) (lowGroupedE2W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (334596134059890277 / 500000000000000000) (241121986924459487 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE2W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE2W_hz36 hx hc) (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (665801103128217919 / 1000000000000000000) (241121986924459487 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE2W_hz35 hx hc) (lowGroupedE2W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (665801103128217919 / 1000000000000000000) (241121986924459487 / 250000000000000000) (ndm x c) := by
    convert (lowGroupedE2W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE2W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE2W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE2W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (3463211788490249 / 7812500000000000) (93023700125438739 / 100000000000000000) ((ndm x c)^2) := bsq (lowGroupedE2W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (106976299874561261 / 100000000000000000) (781748485528186701 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE2W_hz41 hx hc) (lowGroupedE2W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE2W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE2W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (106976299874561261 / 200000000000000000) (784406306035378759 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE2W_hz43 hx hc) (lowGroupedE2W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (106976299874561261 / 200000000000000000) (784406306035378759 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE2W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE2W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (135928750389193431 / 200000000000000000) (6796437519459723 / 10000000000000000) (kdot ((106976299874561261 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (137620898896853551 / 250000000000000000)) (a := (25160720885453477 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (550483595587414203 / 1000000000000000000)) (a := (25160720885453073 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE2W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (157406446805513101 / 200000000000000000) (787032234027565507 / 1000000000000000000) (kdot ((784406306035378759 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (347593104342678737 / 1000000000000000000)) (a := (334528984515215279 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (21724569021417421 / 62500000000000000)) (a := (334528984515215277 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE2W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (135928750389193431 / 200000000000000000) (787032234027565507 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE2W_hz47 hx hc) (lowGroupedE2W_hz48 hx hc).1 (lowGroupedE2W_hz49 hx hc).2

theorem lowGroupedE2W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE2W_hz51 hx hc) (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE2W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (339821875972983577 / 1000000000000000000) (196758058506891377 / 500000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE2W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (339821875972983577 / 1000000000000000000) (98528898988549211 / 250000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE2W_hz54 hx hc) (lowGroupedE2W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (381281025219154481 / 1000000000000000000) (381281025219154483 / 1000000000000000000) ((kdot ((734454819 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE2W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (381281025219154481 / 1000000000000000000) (381880504159568573 / 1000000000000000000) (((kdot ((734454819 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE2W_hz56 hx hc) (lowGroupedE2W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE2W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE2W_hz58 hx hc) (lowGroupedE2W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE2W_hz3 hx hc) (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE2W_hz60 hx hc) (lowGroupedE2W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE2W_hz4 hx hc) (lowGroupedE2W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE2W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE2W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (617479574738431717 / 1000000000000000000) (123592961637719253 / 200000000000000000) (√(((kdot ((734454819 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE2W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (617479574738431717 / 1000000000000000000) (314572574038047607 / 500000000000000000) ((√(((kdot ((734454819 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE2W_hz65 hx hc) (lowGroupedE2W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (617479574738431717 / 1000000000000000000) (315172052978461697 / 500000000000000000) (((√(((kdot ((734454819 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE2W_hz66 hx hc) (lowGroupedE2W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (218311997270865327 / 250000000000000000) (891441183606224317 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((734454819 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE2W_hz4 hx hc) (lowGroupedE2W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (218311997270865327 / 250000000000000000) (891441183606224317 / 1000000000000000000) (neb x (kdot (734454819 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE2W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE2W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE2W_hz4 hx hc) (lowGroupedE2W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE2W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE2W_hz3 hx hc) (lowGroupedE2W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE2W_hz71 hx hc) (lowGroupedE2W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE2W_hz4 hx hc) (lowGroupedE2W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE2W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE2W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE2W_hz4 hx hc) (lowGroupedE2W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE2W_hz76 hx hc) (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE2W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE2W_hz4 hx hc) (lowGroupedE2W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE2W_hz79 hx hc) (lowGroupedE2W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE2W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE2W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE2W_hz70 hx hc) (lowGroupedE2W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE2W_hz82 hx hc) (lowGroupedE2W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE2W_hz4 hx hc) (lowGroupedE2W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE2W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE2W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (582942429381309983 / 1000000000000000000) (627786266140154459 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE2W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (582942429381309983 / 500000000000000000) (627786266140154459 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE2W_hz70 hx hc) (lowGroupedE2W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (2669715428785523 / 125000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE2W_hz87 hx hc) (lowGroupedE2W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE2W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (10823537653752221 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE2W_hz89 hx hc) (lowGroupedE2W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (10823537653752221 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (10823537653752221 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE2W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE2W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE2W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE2W_hz94 hx hc) (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE2W_hz96 hx hc) (lowGroupedE2W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE2W_hz97 hx hc) (lowGroupedE2W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE2W_hz98 hx hc) (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE2W_hz95 hx hc) (lowGroupedE2W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE2W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (22438067607404221 / 500000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE2W_hz93 hx hc) (lowGroupedE2W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (23376534938426423 / 500000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE2W_hz100 hx hc) (lowGroupedE2W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (339821875972983577 / 500000000000000000) (98528898988549211 / 125000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (762562050438308959 / 1000000000000000000) (397333691914633067 / 500000000000000000) ((neb x (kdot (734454819 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE2W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE2W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE2W_hz106 hx hc) (lowGroupedE2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (762562050438308959 / 1000000000000000000) (99372836730142283 / 125000000000000000) (((neb x (kdot (734454819 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE2W_hz105 hx hc) (lowGroupedE2W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (518270533051502147 / 1000000000000000000) (15665753907823651 / 25000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (734454819 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE2W_hz104 hx hc) (lowGroupedE2W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (518270533051502147 / 1000000000000000000) (336691613094899443 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (734454819 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE2W_hz103 hx hc) (lowGroupedE2W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) : B (518270533051502147 / 1000000000000000000) (336691613094899443 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (734454819 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE2W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE2W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (385280557 / 1000000000) (734454819 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (734454819 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (673383227 / 1000000000) :=
  (lowGroupedE2W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE2C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE2C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (230223829 / 500000000) (627256151 / 1000000000) c := hc

theorem lowGroupedE2C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE2C_hz2 hx hc) (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE2C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE2C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE2C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE2C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE2C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE2C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE2C_hz11 hx hc) (lowGroupedE2C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE2C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE2C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (20384721845002039 / 31250000000000000) (32615554952036269 / 50000000000000000) (kdot ((230223829 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (607818329603543077 / 1000000000000000000)) (a := (546148448495220113 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (151954582400885769 / 250000000000000000)) (a := (546148448494183181 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE2C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (53003011439421241 / 250000000000000000) (53003011439421241 / 250000000000000000) (((230223829 / 500000000) : ℝ)^2) := bsq (bpoint ((230223829 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (196996988560578759 / 250000000000000000) (196996988560578759 / 250000000000000000) ((1 : ℝ) - (((230223829 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE2C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (443843427979483277 / 500000000000000000) (177537371191793311 / 200000000000000000) (√((1 : ℝ) - (((230223829 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE2C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (282559502087145627 / 1000000000000000000) (282559502087145629 / 1000000000000000000) ((√((1 : ℝ) - (((230223829 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE2C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (300355117840404091 / 1000000000000000000) (18772194865044253 / 62500000000000000) (((230223829 / 500000000) : ℝ) * (kdot ((230223829 / 500000000)))) := bmul (bpoint ((230223829 / 500000000) : ℝ)) (lowGroupedE2C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (291457309963774859 / 500000000000000000) (582914619927853677 / 1000000000000000000) (((√((1 : ℝ) - (((230223829 / 500000000) : ℝ)^2))) / Real.pi) + (((230223829 / 500000000) : ℝ) * (kdot ((230223829 / 500000000))))) := badd (lowGroupedE2C_hz18 hx hc) (lowGroupedE2C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (291457309963774859 / 500000000000000000) (582914619927853677 / 1000000000000000000) (kappa ((230223829 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE2C_hz20 hx hc)

theorem lowGroupedE2C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (894777605583737 / 1250000000000000) (89477760558373701 / 125000000000000000) (kdot ((627256151 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (478605055575517287 / 1000000000000000000)) (a := (446385625875483131 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (239302527787758643 / 500000000000000000)) (a := (446385625875483121 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE2C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (393450278967334801 / 1000000000000000000) (393450278967334801 / 1000000000000000000) (((627256151 / 1000000000) : ℝ)^2) := bsq (bpoint ((627256151 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (606549721032665199 / 1000000000000000000) (606549721032665199 / 1000000000000000000) ((1 : ℝ) - (((627256151 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE2C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (194703255146239337 / 250000000000000000) (778813020584957349 / 1000000000000000000) (√((1 : ℝ) - (((627256151 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE2C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (123951941970425997 / 500000000000000000) (61975970985212999 / 250000000000000000) ((√((1 : ℝ) - (((627256151 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE2C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (449003805503560783 / 1000000000000000000) (449003805503560789 / 1000000000000000000) (((627256151 / 1000000000) : ℝ) * (kdot ((627256151 / 1000000000)))) := bmul (bpoint ((627256151 / 1000000000) : ℝ)) (lowGroupedE2C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (696907689444412777 / 1000000000000000000) (139381537888882557 / 200000000000000000) (((√((1 : ℝ) - (((627256151 / 1000000000) : ℝ)^2))) / Real.pi) + (((627256151 / 1000000000) : ℝ) * (kdot ((627256151 / 1000000000))))) := badd (lowGroupedE2C_hz26 hx hc) (lowGroupedE2C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (696907689444412777 / 1000000000000000000) (139381537888882557 / 200000000000000000) (kappa ((627256151 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE2C_hz28 hx hc)

theorem lowGroupedE2C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (291457309963774859 / 500000000000000000) (139381537888882557 / 200000000000000000) (kappa c) := bkappa (lowGroupedE2C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE2C_hz21 hx hc).1 (lowGroupedE2C_hz29 hx hc).2

theorem lowGroupedE2C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (60618462111117443 / 200000000000000000) (208542690036225141 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE2C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (60618462111117443 / 100000000000000000) (208542690036225141 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE2C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (60618449611117443 / 100000000000000000) (208542690036225141 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE2C_hz32 hx hc) (lowGroupedE2C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (389289254960618721 / 500000000000000000) (228332372888857539 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE2C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE2C_hz36 hx hc) (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (775187344929674807 / 1000000000000000000) (228332372888857539 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE2C_hz35 hx hc) (lowGroupedE2C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (775187344929674807 / 1000000000000000000) (228332372888857539 / 250000000000000000) (ndm x c) := by
    convert (lowGroupedE2C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE2C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE2C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE2C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (4807323357912949 / 8000000000000000) (166834152028980113 / 200000000000000000) ((ndm x c)^2) := bsq (lowGroupedE2C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (233165847971019887 / 200000000000000000) (1405872660244006649 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE2C_hz41 hx hc) (lowGroupedE2C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE2C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE2C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (582914619927549717 / 1000000000000000000) (44082887614783981 / 62500000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE2C_hz43 hx hc) (lowGroupedE2C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (582914619927549717 / 1000000000000000000) (44082887614783981 / 62500000000000000) (nc1 x c) := by
    convert (lowGroupedE2C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE2C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (698087798239333797 / 1000000000000000000) (698087798239333967 / 1000000000000000000) (kdot ((582914619927549717 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (513314743530622717 / 1000000000000000000)) (a := (47424257754021419 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (128328685882655679 / 250000000000000000)) (a := (18969703101608557 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE2C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (749199463493546499 / 1000000000000000000) (374599731746773251 / 500000000000000000) (kdot ((44082887614783981 / 62500000000000000))) := by
    constructor
    · apply bkdot_lower (q := (415687560133454061 / 1000000000000000000)) (a := (98489140375631633 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (20784378006672703 / 50000000000000000)) (a := (39395656150252653 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE2C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (698087798239333797 / 1000000000000000000) (374599731746773251 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE2C_hz47 hx hc) (lowGroupedE2C_hz48 hx hc).1 (lowGroupedE2C_hz49 hx hc).2

theorem lowGroupedE2C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE2C_hz51 hx hc) (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE2C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (174521949559833449 / 500000000000000000) (374599731746773251 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE2C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (174521949559833449 / 500000000000000000) (375199210687187341 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE2C_hz54 hx hc) (lowGroupedE2C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (894777605583737 / 2500000000000000) (89477760558373701 / 250000000000000000) ((kdot ((627256151 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE2C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (894777605583737 / 2500000000000000) (179255260586954447 / 500000000000000000) (((kdot ((627256151 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE2C_hz56 hx hc) (lowGroupedE2C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE2C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE2C_hz58 hx hc) (lowGroupedE2C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE2C_hz3 hx hc) (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE2C_hz60 hx hc) (lowGroupedE2C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE2C_hz4 hx hc) (lowGroupedE2C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE2C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE2C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (299128334596329573 / 500000000000000000) (119751496220115579 / 200000000000000000) (√(((kdot ((627256151 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE2C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (299128334596329573 / 500000000000000000) (152484455247019211 / 250000000000000000) ((√(((kdot ((627256151 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE2C_hz65 hx hc) (lowGroupedE2C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (299128334596329573 / 500000000000000000) (9549012169826641 / 15625000000000000) (((√(((kdot ((627256151 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE2C_hz66 hx hc) (lowGroupedE2C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (169212539070482551 / 200000000000000000) (216069480285353153 / 250000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((627256151 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE2C_hz4 hx hc) (lowGroupedE2C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (169212539070482551 / 200000000000000000) (216069480285353153 / 250000000000000000) (neb x (kdot (627256151 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE2C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE2C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE2C_hz4 hx hc) (lowGroupedE2C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE2C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE2C_hz3 hx hc) (lowGroupedE2C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE2C_hz71 hx hc) (lowGroupedE2C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE2C_hz4 hx hc) (lowGroupedE2C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE2C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE2C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE2C_hz4 hx hc) (lowGroupedE2C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE2C_hz76 hx hc) (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE2C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE2C_hz4 hx hc) (lowGroupedE2C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE2C_hz79 hx hc) (lowGroupedE2C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE2C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE2C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE2C_hz70 hx hc) (lowGroupedE2C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE2C_hz82 hx hc) (lowGroupedE2C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE2C_hz4 hx hc) (lowGroupedE2C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE2C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE2C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (295399686492583679 / 500000000000000000) (306267534472390389 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE2C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (295399686492583679 / 250000000000000000) (306267534472390389 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE2C_hz70 hx hc) (lowGroupedE2C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (1041943357116387 / 50000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE2C_hz87 hx hc) (lowGroupedE2C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE2C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (10564109509773999 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE2C_hz89 hx hc) (lowGroupedE2C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (10564109509773999 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (10564109509773999 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE2C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE2C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE2C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE2C_hz94 hx hc) (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE2C_hz96 hx hc) (lowGroupedE2C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE2C_hz97 hx hc) (lowGroupedE2C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE2C_hz98 hx hc) (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE2C_hz95 hx hc) (lowGroupedE2C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE2C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (43800504229808129 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE2C_hz93 hx hc) (lowGroupedE2C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (45677438891852533 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE2C_hz100 hx hc) (lowGroupedE2C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (174521949559833449 / 250000000000000000) (375199210687187341 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE2C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (143164416893397919 / 200000000000000000) (373488162486260919 / 500000000000000000) ((neb x (kdot (627256151 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE2C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE2C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE2C_hz106 hx hc) (lowGroupedE2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (143164416893397919 / 200000000000000000) (46705727186524623 / 62500000000000000) (((neb x (kdot (627256151 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE2C_hz105 hx hc) (lowGroupedE2C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (249853331438325593 / 500000000000000000) (280383231599282331 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (627256151 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE2C_hz104 hx hc) (lowGroupedE2C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (249853331438325593 / 500000000000000000) (121288780418083439 / 200000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (627256151 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE2C_hz103 hx hc) (lowGroupedE2C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE2C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) : B (249853331438325593 / 500000000000000000) (121288780418083439 / 200000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (627256151 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE2C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE2C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (230223829 / 500000000) (627256151 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (627256151 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (606443903 / 1000000000) :=
  (lowGroupedE2C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE4W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE4W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (96063767 / 250000000) (733541317 / 1000000000) c := hc

theorem lowGroupedE4W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE4W_hz2 hx hc) (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE4W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE4W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE4W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE4W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE4W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE4W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE4W_hz11 hx hc) (lowGroupedE4W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE4W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE4W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (312770838216078429 / 500000000000000000) (625541676494564789 / 1000000000000000000) (kdot ((96063767 / 250000000))) := by
    constructor
    · apply bkdot_lower (q := (666948594824242483 / 1000000000000000000)) (a := (294098879599071437 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (333474297412121241 / 500000000000000000)) (a := (588197759100112727 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE4W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (9228247330230289 / 62500000000000000) (9228247330230289 / 62500000000000000) (((96063767 / 250000000) : ℝ)^2) := bsq (bpoint ((96063767 / 250000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (53271752669769711 / 62500000000000000) (53271752669769711 / 62500000000000000) ((1 : ℝ) - (((96063767 / 250000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE4W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (461613486240468113 / 500000000000000000) (923226972480936227 / 1000000000000000000) (√((1 : ℝ) - (((96063767 / 250000000) : ℝ)^2))) := bsqrt (lowGroupedE4W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (73468068133053113 / 250000000000000000) (293872272532212453 / 1000000000000000000) ((√((1 : ℝ) - (((96063767 / 250000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE4W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (24036755941427243 / 100000000000000000) (48073511887650599 / 200000000000000000) (((96063767 / 250000000) : ℝ) * (kdot ((96063767 / 250000000)))) := bmul (bpoint ((96063767 / 250000000) : ℝ)) (lowGroupedE4W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (267119915973242441 / 500000000000000000) (66779978996308181 / 125000000000000000) (((√((1 : ℝ) - (((96063767 / 250000000) : ℝ)^2))) / Real.pi) + (((96063767 / 250000000) : ℝ) * (kdot ((96063767 / 250000000))))) := badd (lowGroupedE4W_hz18 hx hc) (lowGroupedE4W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (267119915973242441 / 500000000000000000) (66779978996308181 / 125000000000000000) (kappa ((96063767 / 250000000))) := by rw [kappa_eq]; exact (lowGroupedE4W_hz20 hx hc)

theorem lowGroupedE4W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (762133903268859623 / 1000000000000000000) (6097071226150877 / 8000000000000000) (kdot ((733541317 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (15682230442957047 / 40000000000000000)) (a := (373639191014314869 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (196027880536963087 / 500000000000000000)) (a := (373639191014314867 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE4W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (538082863746094489 / 1000000000000000000) (538082863746094489 / 1000000000000000000) (((733541317 / 1000000000) : ℝ)^2) := bsq (bpoint ((733541317 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (461917136253905511 / 1000000000000000000) (461917136253905511 / 1000000000000000000) ((1 : ℝ) - (((733541317 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE4W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (339822430194765657 / 500000000000000000) (135928972077906263 / 200000000000000000) (√((1 : ℝ) - (((733541317 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE4W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (216337678155990013 / 1000000000000000000) (108168839077995007 / 500000000000000000) ((√((1 : ℝ) - (((733541317 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE4W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (139764176783547473 / 250000000000000000) (111811341426837979 / 200000000000000000) (((733541317 / 1000000000) : ℝ) * (kdot ((733541317 / 1000000000)))) := bmul (bpoint ((733541317 / 1000000000) : ℝ)) (lowGroupedE4W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (155078877058035981 / 200000000000000000) (775394385290179909 / 1000000000000000000) (((√((1 : ℝ) - (((733541317 / 1000000000) : ℝ)^2))) / Real.pi) + (((733541317 / 1000000000) : ℝ) * (kdot ((733541317 / 1000000000))))) := badd (lowGroupedE4W_hz26 hx hc) (lowGroupedE4W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (155078877058035981 / 200000000000000000) (775394385290179909 / 1000000000000000000) (kappa ((733541317 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE4W_hz28 hx hc)

theorem lowGroupedE4W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (267119915973242441 / 500000000000000000) (775394385290179909 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE4W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE4W_hz21 hx hc).1 (lowGroupedE4W_hz29 hx hc).2

theorem lowGroupedE4W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (224605614709820091 / 1000000000000000000) (232880084026757559 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE4W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (224605614709820091 / 500000000000000000) (232880084026757559 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE4W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (224605552209820091 / 500000000000000000) (232880084026757559 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE4W_hz32 hx hc) (lowGroupedE4W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (167558031816524723 / 250000000000000000) (965153011758773013 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE4W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE4W_hz36 hx hc) (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (666840962274536257 / 1000000000000000000) (965153011758773013 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE4W_hz35 hx hc) (lowGroupedE4W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (666840962274536257 / 1000000000000000000) (965153011758773013 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE4W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE4W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE4W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE4W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (444676868967229487 / 1000000000000000000) (465760168053515119 / 500000000000000000) ((ndm x c)^2) := bsq (lowGroupedE4W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (534239831946484881 / 500000000000000000) (1562111211015895787 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE4W_hz41 hx hc) (lowGroupedE4W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE4W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE4W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (534239831946484881 / 1000000000000000000) (391855535166639737 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE4W_hz43 hx hc) (lowGroupedE4W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (534239831946484881 / 1000000000000000000) (391855535166639737 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE4W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE4W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (67940207425045527 / 100000000000000000) (679402074250460647 / 1000000000000000000) (kdot ((534239831946484881 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (137744591118364277 / 250000000000000000)) (a := (62949255518180983 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (550978364473457107 / 1000000000000000000)) (a := (25179702207271971 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE4W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (196668923172631337 / 250000000000000000) (15733513853810507 / 20000000000000000) (kdot ((391855535166639737 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (69644189339491533 / 200000000000000000)) (a := (167544519168894249 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (85014879564809 / 244140625000000)) (a := (20943064896111781 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE4W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (67940207425045527 / 100000000000000000) (15733513853810507 / 20000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE4W_hz47 hx hc) (lowGroupedE4W_hz48 hx hc).1 (lowGroupedE4W_hz49 hx hc).2

theorem lowGroupedE4W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE4W_hz51 hx hc) (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE4W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (67940207425045527 / 200000000000000000) (15733513853810507 / 40000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE4W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (67940207425045527 / 200000000000000000) (78787465057135353 / 200000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE4W_hz54 hx hc) (lowGroupedE4W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (381066951634429811 / 1000000000000000000) (381066951634429813 / 1000000000000000000) ((kdot ((733541317 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE4W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (381066951634429811 / 1000000000000000000) (381666430574843903 / 1000000000000000000) (((kdot ((733541317 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE4W_hz56 hx hc) (lowGroupedE4W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE4W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE4W_hz58 hx hc) (lowGroupedE4W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE4W_hz3 hx hc) (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE4W_hz60 hx hc) (lowGroupedE4W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE4W_hz4 hx hc) (lowGroupedE4W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE4W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE4W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (617306205731345139 / 1000000000000000000) (123558315070228099 / 200000000000000000) (√(((kdot ((733541317 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE4W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (617306205731345139 / 1000000000000000000) (157242978809659861 / 250000000000000000) ((√(((kdot ((733541317 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE4W_hz65 hx hc) (lowGroupedE4W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (617306205731345139 / 1000000000000000000) (78771359139933453 / 125000000000000000) (((√(((kdot ((733541317 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE4W_hz66 hx hc) (lowGroupedE4W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (109125351035293039 / 125000000000000000) (891196195378045993 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((733541317 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE4W_hz4 hx hc) (lowGroupedE4W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (109125351035293039 / 125000000000000000) (891196195378045993 / 1000000000000000000) (neb x (kdot (733541317 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE4W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE4W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE4W_hz4 hx hc) (lowGroupedE4W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE4W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE4W_hz3 hx hc) (lowGroupedE4W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE4W_hz71 hx hc) (lowGroupedE4W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE4W_hz4 hx hc) (lowGroupedE4W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE4W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE4W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE4W_hz4 hx hc) (lowGroupedE4W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE4W_hz76 hx hc) (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE4W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE4W_hz4 hx hc) (lowGroupedE4W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE4W_hz79 hx hc) (lowGroupedE4W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE4W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE4W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE4W_hz70 hx hc) (lowGroupedE4W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE4W_hz82 hx hc) (lowGroupedE4W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE4W_hz4 hx hc) (lowGroupedE4W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE4W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE4W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (29141938727769453 / 50000000000000000) (313822133256115623 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE4W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (29141938727769453 / 25000000000000000) (313822133256115623 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE4W_hz70 hx hc) (lowGroupedE4W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (213528925046269 / 10000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE4W_hz87 hx hc) (lowGroupedE4W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE4W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (10821122190923579 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE4W_hz89 hx hc) (lowGroupedE4W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (10821122190923579 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (10821122190923579 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE4W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE4W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE4W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE4W_hz94 hx hc) (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE4W_hz96 hx hc) (lowGroupedE4W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE4W_hz97 hx hc) (lowGroupedE4W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE4W_hz98 hx hc) (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE4W_hz95 hx hc) (lowGroupedE4W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE4W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (44866120315801101 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE4W_hz93 hx hc) (lowGroupedE4W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (9348610995569101 / 200000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE4W_hz100 hx hc) (lowGroupedE4W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (67940207425045527 / 100000000000000000) (78787465057135353 / 100000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (381066951634429809 / 500000000000000000) (794230658656304327 / 1000000000000000000) ((neb x (kdot (733541317 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE4W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE4W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE4W_hz106 hx hc) (lowGroupedE4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (381066951634429809 / 500000000000000000) (794545968668176457 / 1000000000000000000) (((neb x (kdot (733541317 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE4W_hz105 hx hc) (lowGroupedE4W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (32362209671091191 / 62500000000000000) (626002627427317137 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (733541317 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE4W_hz104 hx hc) (lowGroupedE4W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (32362209671091191 / 62500000000000000) (336372841202581321 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (733541317 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE4W_hz103 hx hc) (lowGroupedE4W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) : B (32362209671091191 / 62500000000000000) (336372841202581321 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (733541317 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE4W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE4W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (96063767 / 250000000) (733541317 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (733541317 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (672745683 / 1000000000) :=
  (lowGroupedE4W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE4C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE4C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (28714803 / 62500000) (626282771 / 1000000000) c := hc

theorem lowGroupedE4C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE4C_hz2 hx hc) (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE4C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE4C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE4C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE4C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE4C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE4C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE4C_hz11 hx hc) (lowGroupedE4C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE4C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE4C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (325974373062163413 / 500000000000000000) (325974373062514879 / 500000000000000000) (kdot ((28714803 / 62500000))) := by
    constructor
    · apply bkdot_lower (q := (304299031340149777 / 500000000000000000)) (a := (273358815562132723 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (608598062680299553 / 1000000000000000000)) (a := (109343526224632257 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE4C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (824539911328809 / 3906250000000000) (824539911328809 / 3906250000000000) (((28714803 / 62500000) : ℝ)^2) := bsq (bpoint ((28714803 / 62500000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (3081710088671191 / 3906250000000000) (3081710088671191 / 3906250000000000) ((1 : ℝ) - (((28714803 / 62500000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE4C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (888210438297042811 / 1000000000000000000) (222052609574260703 / 250000000000000000) (√((1 : ℝ) - (((28714803 / 62500000) : ℝ)^2))) := bsqrt (lowGroupedE4C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (70681540880396631 / 250000000000000000) (11309046540863461 / 40000000000000000) ((√((1 : ℝ) - (((28714803 / 62500000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE4C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (299529276976912933 / 1000000000000000000) (149764638488617943 / 500000000000000000) (((28714803 / 62500000) : ℝ) * (kdot ((28714803 / 62500000)))) := bmul (bpoint ((28714803 / 62500000) : ℝ)) (lowGroupedE4C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (582255440498499457 / 1000000000000000000) (582255440498822411 / 1000000000000000000) (((√((1 : ℝ) - (((28714803 / 62500000) : ℝ)^2))) / Real.pi) + (((28714803 / 62500000) : ℝ) * (kdot ((28714803 / 62500000))))) := badd (lowGroupedE4C_hz18 hx hc) (lowGroupedE4C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (582255440498499457 / 1000000000000000000) (582255440498822411 / 1000000000000000000) (kappa ((28714803 / 62500000))) := by rw [kappa_eq]; exact (lowGroupedE4C_hz20 hx hc)

theorem lowGroupedE4C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (22357014147894139 / 31250000000000000) (89428056591576557 / 125000000000000000) (kdot ((626282771 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (479372955969631809 / 1000000000000000000)) (a := (223505112171629923 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (7490202437025497 / 15625000000000000)) (a := (89402044868651967 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE4C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (392230109251438441 / 1000000000000000000) (392230109251438441 / 1000000000000000000) (((626282771 / 1000000000) : ℝ)^2) := bsq (bpoint ((626282771 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (607769890748561559 / 1000000000000000000) (607769890748561559 / 1000000000000000000) ((1 : ℝ) - (((626282771 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE4C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (779595979176753809 / 1000000000000000000) (77959597917675381 / 100000000000000000) (√((1 : ℝ) - (((626282771 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE4C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (248153107401093347 / 1000000000000000000) (62038276850273337 / 250000000000000000) ((√((1 : ℝ) - (((626282771 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE4C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (224029004349269523 / 500000000000000000) (112014502174634763 / 250000000000000000) (((626282771 / 1000000000) : ℝ) * (kdot ((626282771 / 1000000000)))) := bmul (bpoint ((626282771 / 1000000000) : ℝ)) (lowGroupedE4C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (696211116099632393 / 1000000000000000000) (1740527790249081 / 2500000000000000) (((√((1 : ℝ) - (((626282771 / 1000000000) : ℝ)^2))) / Real.pi) + (((626282771 / 1000000000) : ℝ) * (kdot ((626282771 / 1000000000))))) := badd (lowGroupedE4C_hz26 hx hc) (lowGroupedE4C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (696211116099632393 / 1000000000000000000) (1740527790249081 / 2500000000000000) (kappa ((626282771 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE4C_hz28 hx hc)

theorem lowGroupedE4C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (582255440498499457 / 1000000000000000000) (1740527790249081 / 2500000000000000) (kappa c) := bkappa (lowGroupedE4C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE4C_hz21 hx hc).1 (lowGroupedE4C_hz29 hx hc).2

theorem lowGroupedE4C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (759472209750919 / 2500000000000000) (417744559501500543 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE4C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (759472209750919 / 1250000000000000) (417744559501500543 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE4C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (759472053500919 / 1250000000000000) (417744559501500543 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE4C_hz32 hx hc) (lowGroupedE4C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (389736334847270559 / 500000000000000000) (914050938954170697 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE4C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE4C_hz36 hx hc) (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (776081504702978483 / 1000000000000000000) (914050938954170697 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE4C_hz35 hx hc) (lowGroupedE4C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (776081504702978483 / 1000000000000000000) (914050938954170697 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE4C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE4C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE4C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE4C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (602302501942039213 / 1000000000000000000) (835489119003001087 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE4C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (1164510880996998913 / 1000000000000000000) (1404485578041086061 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE4C_hz41 hx hc) (lowGroupedE4C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE4C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE4C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (4548870628894527 / 7812500000000000) (352315151402825961 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE4C_hz43 hx hc) (lowGroupedE4C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (4548870628894527 / 7812500000000000) (352315151402825961 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE4C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE4C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (174457409958950147 / 250000000000000000) (348914819917900383 / 500000000000000000) (kdot ((4548870628894527 / 7812500000000000))) := by
    constructor
    · apply bkdot_lower (q := (128456803570470139 / 250000000000000000)) (a := (47464809181221539 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (102765442856376111 / 200000000000000000)) (a := (59331011476526889 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE4C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (149777427232430917 / 200000000000000000) (187221784040538647 / 250000000000000000) (kdot ((352315151402825961 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (416263054412956929 / 1000000000000000000)) (a := (394447164127434603 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1626027556300613 / 3906250000000000)) (a := (394447164127434601 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE4C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (174457409958950147 / 250000000000000000) (187221784040538647 / 250000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE4C_hz47 hx hc) (lowGroupedE4C_hz48 hx hc).1 (lowGroupedE4C_hz49 hx hc).2

theorem lowGroupedE4C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE4C_hz51 hx hc) (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE4C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (174457409958950147 / 500000000000000000) (187221784040538647 / 500000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE4C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (174457409958950147 / 500000000000000000) (46880380877686423 / 125000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE4C_hz54 hx hc) (lowGroupedE4C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (22357014147894139 / 62500000000000000) (89428056591576557 / 250000000000000000) ((kdot ((626282771 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE4C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (22357014147894139 / 62500000000000000) (179155852653360159 / 500000000000000000) (((kdot ((626282771 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE4C_hz56 hx hc) (lowGroupedE4C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE4C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE4C_hz58 hx hc) (lowGroupedE4C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE4C_hz3 hx hc) (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE4C_hz60 hx hc) (lowGroupedE4C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE4C_hz4 hx hc) (lowGroupedE4C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE4C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE4C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (598090483427304019 / 1000000000000000000) (299295717187333103 / 500000000000000000) (√(((kdot ((626282771 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE4C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (598090483427304019 / 1000000000000000000) (121954354852433031 / 200000000000000000) ((√(((kdot ((626282771 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE4C_hz65 hx hc) (lowGroupedE4C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (598090483427304019 / 1000000000000000000) (122194146428598667 / 200000000000000000) (((√(((kdot ((626282771 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE4C_hz66 hx hc) (lowGroupedE4C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (422913836594587091 / 500000000000000000) (864043095609640653 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((626282771 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE4C_hz4 hx hc) (lowGroupedE4C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (422913836594587091 / 500000000000000000) (864043095609640653 / 1000000000000000000) (neb x (kdot (626282771 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE4C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE4C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE4C_hz4 hx hc) (lowGroupedE4C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE4C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE4C_hz3 hx hc) (lowGroupedE4C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE4C_hz71 hx hc) (lowGroupedE4C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE4C_hz4 hx hc) (lowGroupedE4C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE4C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE4C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE4C_hz4 hx hc) (lowGroupedE4C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE4C_hz76 hx hc) (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE4C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE4C_hz4 hx hc) (lowGroupedE4C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE4C_hz79 hx hc) (lowGroupedE4C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE4C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE4C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE4C_hz70 hx hc) (lowGroupedE4C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE4C_hz82 hx hc) (lowGroupedE4C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE4C_hz4 hx hc) (lowGroupedE4C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE4C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE4C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (118138024347438669 / 200000000000000000) (612407582433048737 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE4C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (118138024347438669 / 100000000000000000) (612407582433048737 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE4C_hz70 hx hc) (lowGroupedE4C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (20834529962931629 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE4C_hz87 hx hc) (lowGroupedE4C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE4C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (21123881840151887 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE4C_hz89 hx hc) (lowGroupedE4C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (21123881840151887 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (21123881840151887 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE4C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE4C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE4C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE4C_hz94 hx hc) (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE4C_hz96 hx hc) (lowGroupedE4C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE4C_hz97 hx hc) (lowGroupedE4C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE4C_hz98 hx hc) (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE4C_hz95 hx hc) (lowGroupedE4C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE4C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (21895756453336257 / 500000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE4C_hz93 hx hc) (lowGroupedE4C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (22834223784358459 / 500000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE4C_hz100 hx hc) (lowGroupedE4C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (174457409958950147 / 250000000000000000) (46880380877686423 / 62500000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE4C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (143084890546522489 / 200000000000000000) (746570471070690619 / 1000000000000000000) ((neb x (kdot (626282771 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE4C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE4C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE4C_hz106 hx hc) (lowGroupedE4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (143084890546522489 / 200000000000000000) (746885781082562749 / 1000000000000000000) (((neb x (kdot (626282771 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE4C_hz105 hx hc) (lowGroupedE4C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (124811097045030921 / 250000000000000000) (560228638228461803 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (626282771 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE4C_hz104 hx hc) (lowGroupedE4C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (124811097045030921 / 250000000000000000) (605897085797178721 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (626282771 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE4C_hz103 hx hc) (lowGroupedE4C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE4C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) : B (124811097045030921 / 250000000000000000) (605897085797178721 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (626282771 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE4C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE4C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (28714803 / 62500000) (626282771 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (626282771 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (302948543 / 500000000) :=
  (lowGroupedE4C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE6W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE6W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (191615063 / 500000000) (366313529 / 500000000) c := hc

theorem lowGroupedE6W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE6W_hz2 hx hc) (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE6W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE6W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE6W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE6W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE6W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE6W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE6W_hz11 hx hc) (lowGroupedE6W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE6W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE6W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (625188378803927347 / 1000000000000000000) (625188378870121181 / 1000000000000000000) (kdot ((191615063 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (667750707336422697 / 1000000000000000000)) (a := (294376358907415569 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (83468838417052837 / 125000000000000000)) (a := (588752717710854109 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE6W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (36716332368493969 / 250000000000000000) (36716332368493969 / 250000000000000000) (((191615063 / 500000000) : ℝ)^2) := bsq (bpoint ((191615063 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (213283667631506031 / 250000000000000000) (213283667631506031 / 250000000000000000) ((1 : ℝ) - (((191615063 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE6W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (92365289504554909 / 100000000000000000) (923652895045549091 / 1000000000000000000) (√((1 : ℝ) - (((191615063 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE6W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (294007847895277481 / 1000000000000000000) (147003923947638741 / 500000000000000000) ((√((1 : ℝ) - (((191615063 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE6W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (119795510591382403 / 500000000000000000) (119795510604066139 / 500000000000000000) (((191615063 / 500000000) : ℝ) * (kdot ((191615063 / 500000000)))) := bmul (bpoint ((191615063 / 500000000) : ℝ)) (lowGroupedE6W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (533598869078042287 / 1000000000000000000) (3334992931896311 / 6250000000000000) (((√((1 : ℝ) - (((191615063 / 500000000) : ℝ)^2))) / Real.pi) + (((191615063 / 500000000) : ℝ) * (kdot ((191615063 / 500000000))))) := badd (lowGroupedE6W_hz18 hx hc) (lowGroupedE6W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (533598869078042287 / 1000000000000000000) (3334992931896311 / 6250000000000000) (kappa ((191615063 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE6W_hz20 hx hc)

theorem lowGroupedE6W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (380853011363611017 / 500000000000000000) (190426505681805509 / 250000000000000000) (kdot ((366313529 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (196415693870404369 / 500000000000000000)) (a := (74862260839485241 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (392831387740808737 / 1000000000000000000)) (a := (374311304197426203 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE6W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (134185601528433841 / 250000000000000000) (134185601528433841 / 250000000000000000) (((366313529 / 500000000) : ℝ)^2) := bsq (bpoint ((366313529 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (115814398471566159 / 250000000000000000) (115814398471566159 / 250000000000000000) ((1 : ℝ) - (((366313529 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE6W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (680630291631414709 / 1000000000000000000) (68063029163141471 / 100000000000000000) (√((1 : ℝ) - (((366313529 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE6W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (54162837665608967 / 250000000000000000) (216651350662435869 / 1000000000000000000) ((√((1 : ℝ) - (((366313529 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE6W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (111609288498305163 / 200000000000000000) (558046442491525817 / 1000000000000000000) (((366313529 / 500000000) : ℝ) * (kdot ((366313529 / 500000000)))) := bmul (bpoint ((366313529 / 500000000) : ℝ)) (lowGroupedE6W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (774697793153961683 / 1000000000000000000) (387348896576980843 / 500000000000000000) (((√((1 : ℝ) - (((366313529 / 500000000) : ℝ)^2))) / Real.pi) + (((366313529 / 500000000) : ℝ) * (kdot ((366313529 / 500000000))))) := badd (lowGroupedE6W_hz26 hx hc) (lowGroupedE6W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (774697793153961683 / 1000000000000000000) (387348896576980843 / 500000000000000000) (kappa ((366313529 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE6W_hz28 hx hc)

theorem lowGroupedE6W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (533598869078042287 / 1000000000000000000) (387348896576980843 / 500000000000000000) (kappa c) := bkappa (lowGroupedE6W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE6W_hz21 hx hc).1 (lowGroupedE6W_hz29 hx hc).2

theorem lowGroupedE6W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (112651103423019157 / 500000000000000000) (466401130921957713 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE6W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (112651103423019157 / 250000000000000000) (466401130921957713 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE6W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (112651072173019157 / 250000000000000000) (466401130921957713 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE6W_hz32 hx hc) (lowGroupedE6W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (671270652339335201 / 1000000000000000000) (193163377672261201 / 200000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE6W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE6W_hz36 hx hc) (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (333939743673886283 / 500000000000000000) (193163377672261201 / 200000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE6W_hz35 hx hc) (lowGroupedE6W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (333939743673886283 / 500000000000000000) (193163377672261201 / 200000000000000000) (ndm x c) := by
    convert (lowGroupedE6W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE6W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE6W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE6W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (89212601923984699 / 200000000000000000) (932802261843915427 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE6W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (1067197738156084573 / 1000000000000000000) (1560725070363201779 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE6W_hz41 hx hc) (lowGroupedE6W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE6W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE6W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (266799434539021143 / 500000000000000000) (391507821839030747 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE6W_hz43 hx hc) (lowGroupedE6W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (266799434539021143 / 500000000000000000) (391507821839030747 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE6W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE6W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (169790194409904649 / 250000000000000000) (679160777639624213 / 1000000000000000000) (kdot ((266799434539021143 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (137868139931097149 / 250000000000000000)) (a := (50397307197541817 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (110294511944877719 / 200000000000000000)) (a := (125993267993852337 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE6W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (786319556824872589 / 1000000000000000000) (786319556824872591 / 1000000000000000000) (kdot ((391507821839030747 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (174424159782211389 / 500000000000000000)) (a := (335648455247395773 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (348848319564422777 / 1000000000000000000)) (a := (335648455247395771 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE6W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (169790194409904649 / 250000000000000000) (786319556824872591 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE6W_hz47 hx hc) (lowGroupedE6W_hz48 hx hc).1 (lowGroupedE6W_hz49 hx hc).2

theorem lowGroupedE6W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE6W_hz51 hx hc) (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE6W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (169790194409904649 / 500000000000000000) (49144972301554537 / 125000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE6W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (169790194409904649 / 500000000000000000) (196879628676425193 / 500000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE6W_hz54 hx hc) (lowGroupedE6W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (380853011363611017 / 1000000000000000000) (190426505681805509 / 500000000000000000) ((kdot ((366313529 / 500000000))) / (2 : ℝ)) := bdiv (lowGroupedE6W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (380853011363611017 / 1000000000000000000) (95363122576006277 / 250000000000000000) (((kdot ((366313529 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE6W_hz56 hx hc) (lowGroupedE6W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE6W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE6W_hz58 hx hc) (lowGroupedE6W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE6W_hz3 hx hc) (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE6W_hz60 hx hc) (lowGroupedE6W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE6W_hz4 hx hc) (lowGroupedE6W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE6W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE6W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (617132896031001589 / 1000000000000000000) (617618401850224269 / 1000000000000000000) (√(((kdot ((366313529 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE6W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (617132896031001589 / 1000000000000000000) (314399370868861609 / 500000000000000000) ((√(((kdot ((366313529 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE6W_hz65 hx hc) (lowGroupedE6W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (617132896031001589 / 1000000000000000000) (314998849809275699 / 500000000000000000) (((√(((kdot ((366313529 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE6W_hz66 hx hc) (lowGroupedE6W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (872757711353627647 / 1000000000000000000) (890951291064406637 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((366313529 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE6W_hz4 hx hc) (lowGroupedE6W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (872757711353627647 / 1000000000000000000) (890951291064406637 / 1000000000000000000) (neb x (kdot (366313529 / 500000000)/2+√23*x)) := by
    convert (lowGroupedE6W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE6W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE6W_hz4 hx hc) (lowGroupedE6W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE6W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE6W_hz3 hx hc) (lowGroupedE6W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE6W_hz71 hx hc) (lowGroupedE6W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE6W_hz4 hx hc) (lowGroupedE6W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE6W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE6W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE6W_hz4 hx hc) (lowGroupedE6W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE6W_hz76 hx hc) (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE6W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE6W_hz4 hx hc) (lowGroupedE6W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE6W_hz79 hx hc) (lowGroupedE6W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE6W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE6W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE6W_hz70 hx hc) (lowGroupedE6W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE6W_hz82 hx hc) (lowGroupedE6W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE6W_hz4 hx hc) (lowGroupedE6W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE6W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE6W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (582735264781366477 / 1000000000000000000) (627502396292516469 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE6W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (582735264781366477 / 500000000000000000) (627502396292516469 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE6W_hz70 hx hc) (lowGroupedE6W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (333563530961351 / 15625000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE6W_hz87 hx hc) (lowGroupedE6W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE6W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (10818708929373361 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE6W_hz89 hx hc) (lowGroupedE6W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (10818708929373361 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (10818708929373361 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE6W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE6W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE6W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE6W_hz94 hx hc) (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE6W_hz96 hx hc) (lowGroupedE6W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE6W_hz97 hx hc) (lowGroupedE6W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE6W_hz98 hx hc) (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE6W_hz95 hx hc) (lowGroupedE6W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE6W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (44856114543649633 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE6W_hz93 hx hc) (lowGroupedE6W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (46733049205694037 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE6W_hz100 hx hc) (lowGroupedE6W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (169790194409904649 / 250000000000000000) (196879628676425193 / 250000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (47606626420451377 / 62500000000000000) (396897101524666517 / 500000000000000000) ((neb x (kdot (366313529 / 500000000)/2+√23*x))^2) := bsq (lowGroupedE6W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE6W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE6W_hz106 hx hc) (lowGroupedE6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (47606626420451377 / 62500000000000000) (198527378265301291 / 250000000000000000) (((neb x (kdot (366313529 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE6W_hz105 hx hc) (lowGroupedE6W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (517320854728201111 / 1000000000000000000) (625375944239627579 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (366313529 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE6W_hz104 hx hc) (lowGroupedE6W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (517320854728201111 / 1000000000000000000) (42006812090332601 / 62500000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (366313529 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE6W_hz103 hx hc) (lowGroupedE6W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) : B (517320854728201111 / 1000000000000000000) (42006812090332601 / 62500000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (366313529 / 500000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE6W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE6W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (191615063 / 500000000) (366313529 / 500000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (366313529 / 500000000)/2+√23*x)^2) (np1 x) ≤ (336054497 / 500000000) :=
  (lowGroupedE6W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE6C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE6C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (458426349 / 1000000000) (156327257 / 250000000) c := hc

theorem lowGroupedE6C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE6C_hz2 hx hc) (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE6C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE6C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE6C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE6C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE6C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE6C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE6C_hz11 hx hc) (lowGroupedE6C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE6C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE6C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (162896679459132343 / 250000000000000000) (40724169864829863 / 62500000000000000) (kdot ((458426349 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (121875527373655939 / 200000000000000000)) (a := (547286303828933533 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (304688818434139847 / 500000000000000000)) (a := (109457260765551579 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE6C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (210154717457469801 / 1000000000000000000) (210154717457469801 / 1000000000000000000) (((458426349 / 1000000000) : ℝ)^2) := bsq (bpoint ((458426349 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (789845282542530199 / 1000000000000000000) (789845282542530199 / 1000000000000000000) ((1 : ℝ) - (((458426349 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE6C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (222183100525013237 / 250000000000000000) (888732402100052949 / 1000000000000000000) (√((1 : ℝ) - (((458426349 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE6C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (282892309760314739 / 1000000000000000000) (14144615488015737 / 50000000000000000) ((√((1 : ℝ) - (((458426349 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE6C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (149352260057346669 / 500000000000000000) (149352260057518221 / 500000000000000000) (((458426349 / 1000000000) : ℝ) * (kdot ((458426349 / 1000000000)))) := bmul (bpoint ((458426349 / 1000000000) : ℝ)) (lowGroupedE6C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (581596829875008077 / 1000000000000000000) (290798414937675591 / 500000000000000000) (((√((1 : ℝ) - (((458426349 / 1000000000) : ℝ)^2))) / Real.pi) + (((458426349 / 1000000000) : ℝ) * (kdot ((458426349 / 1000000000))))) := badd (lowGroupedE6C_hz18 hx hc) (lowGroupedE6C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (581596829875008077 / 1000000000000000000) (290798414937675591 / 500000000000000000) (kappa ((458426349 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE6C_hz20 hx hc)

theorem lowGroupedE6C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (178756767892597159 / 250000000000000000) (178756767892597161 / 250000000000000000) (kdot ((156327257 / 250000000))) := by
    constructor
    · apply bkdot_lower (q := (3000880200051241 / 6250000000000000)) (a := (447634429213218497 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (480140832008198559 / 1000000000000000000)) (a := (223817214606609243 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE6C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (24438211281144049 / 62500000000000000) (24438211281144049 / 62500000000000000) (((156327257 / 250000000) : ℝ)^2) := bsq (bpoint ((156327257 / 250000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (38061788718855951 / 62500000000000000) (38061788718855951 / 62500000000000000) ((1 : ℝ) - (((156327257 / 250000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE6C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (97547153621794561 / 125000000000000000) (780377228974356489 / 1000000000000000000) (√((1 : ℝ) - (((156327257 / 250000000) : ℝ)^2))) := bsqrt (lowGroupedE6C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (49680357387049873 / 200000000000000000) (124200893467624683 / 500000000000000000) ((√((1 : ℝ) - (((156327257 / 250000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE6C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (447112883117366151 / 1000000000000000000) (447112883117366157 / 1000000000000000000) (((156327257 / 250000000) : ℝ) * (kdot ((156327257 / 250000000)))) := bmul (bpoint ((156327257 / 250000000) : ℝ)) (lowGroupedE6C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (173878667513153879 / 250000000000000000) (695514670052615523 / 1000000000000000000) (((√((1 : ℝ) - (((156327257 / 250000000) : ℝ)^2))) / Real.pi) + (((156327257 / 250000000) : ℝ) * (kdot ((156327257 / 250000000))))) := badd (lowGroupedE6C_hz26 hx hc) (lowGroupedE6C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (173878667513153879 / 250000000000000000) (695514670052615523 / 1000000000000000000) (kappa ((156327257 / 250000000))) := by rw [kappa_eq]; exact (lowGroupedE6C_hz28 hx hc)

theorem lowGroupedE6C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (581596829875008077 / 1000000000000000000) (695514670052615523 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE6C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE6C_hz21 hx hc).1 (lowGroupedE6C_hz29 hx hc).2

theorem lowGroupedE6C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (304485329947384477 / 1000000000000000000) (418403170124991923 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE6C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (304485329947384477 / 500000000000000000) (418403170124991923 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE6C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (304485267447384477 / 500000000000000000) (418403170124991923 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE6C_hz32 hx hc) (lowGroupedE6C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (780365641795414359 / 1000000000000000000) (914771195572960663 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE6C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE6C_hz36 hx hc) (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (194243619200962931 / 250000000000000000) (914771195572960663 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE6C_hz35 hx hc) (lowGroupedE6C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (194243619200962931 / 250000000000000000) (914771195572960663 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE6C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE6C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE6C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE6C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (7546116720057739 / 12500000000000000) (836806340249983847 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE6C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (1163193659750016153 / 1000000000000000000) (701549371189253077 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE6C_hz41 hx hc) (lowGroupedE6C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE6C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE6C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (145399207468752019 / 250000000000000000) (703934527464029461 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE6C_hz43 hx hc) (lowGroupedE6C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (145399207468752019 / 250000000000000000) (703934527464029461 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE6C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE6C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (697571853864782531 / 1000000000000000000) (348785926932391359 / 500000000000000000) (kdot ((145399207468752019 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (1607309871438033 / 3125000000000000)) (a := (47505302106858981 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (514339158860170559 / 1000000000000000000)) (a := (237526510534294759 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE6C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (374287584144388593 / 500000000000000000) (187143792072194297 / 250000000000000000) (kdot ((703934527464029461 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (416838121051941179 / 1000000000000000000)) (a := (394937202117013837 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (208419060525970589 / 500000000000000000)) (a := (78987440423402767 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE6C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (697571853864782531 / 1000000000000000000) (187143792072194297 / 250000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE6C_hz47 hx hc) (lowGroupedE6C_hz48 hx hc).1 (lowGroupedE6C_hz49 hx hc).2

theorem lowGroupedE6C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE6C_hz51 hx hc) (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE6C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (69757185386478253 / 200000000000000000) (187143792072194297 / 500000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE6C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (69757185386478253 / 200000000000000000) (93721765771200671 / 250000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE6C_hz54 hx hc) (lowGroupedE6C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (178756767892597159 / 500000000000000000) (178756767892597161 / 500000000000000000) ((kdot ((156327257 / 250000000))) / (2 : ℝ)) := bdiv (lowGroupedE6C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (178756767892597159 / 500000000000000000) (89528253681402103 / 250000000000000000) (((kdot ((156327257 / 250000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE6C_hz56 hx hc) (lowGroupedE6C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE6C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE6C_hz58 hx hc) (lowGroupedE6C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE6C_hz3 hx hc) (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE6C_hz60 hx hc) (lowGroupedE6C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE6C_hz4 hx hc) (lowGroupedE6C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE6C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE6C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (149481089060036771 / 250000000000000000) (598425446255094013 / 1000000000000000000) (√(((kdot ((156327257 / 250000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE6C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (149481089060036771 / 250000000000000000) (304802893071296481 / 500000000000000000) ((√(((kdot ((156327257 / 250000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE6C_hz65 hx hc) (lowGroupedE6C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (149481089060036771 / 250000000000000000) (305402372011710571 / 500000000000000000) (((√(((kdot ((156327257 / 250000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE6C_hz66 hx hc) (lowGroupedE6C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (845592733868017951 / 1000000000000000000) (863808352959748851 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((156327257 / 250000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE6C_hz4 hx hc) (lowGroupedE6C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (845592733868017951 / 1000000000000000000) (863808352959748851 / 1000000000000000000) (neb x (kdot (156327257 / 250000000)/2+√23*x)) := by
    convert (lowGroupedE6C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE6C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE6C_hz4 hx hc) (lowGroupedE6C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE6C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE6C_hz3 hx hc) (lowGroupedE6C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE6C_hz71 hx hc) (lowGroupedE6C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE6C_hz4 hx hc) (lowGroupedE6C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE6C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE6C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE6C_hz4 hx hc) (lowGroupedE6C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE6C_hz76 hx hc) (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE6C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE6C_hz4 hx hc) (lowGroupedE6C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE6C_hz79 hx hc) (lowGroupedE6C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE6C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE6C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE6C_hz70 hx hc) (lowGroupedE6C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE6C_hz82 hx hc) (lowGroupedE6C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE6C_hz4 hx hc) (lowGroupedE6C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE6C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE6C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (295290503967021967 / 500000000000000000) (306140108073412477 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE6C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (295290503967021967 / 250000000000000000) (306140108073412477 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE6C_hz70 hx hc) (lowGroupedE6C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (5207549218422637 / 250000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE6C_hz87 hx hc) (lowGroupedE6C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE6C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (10559774375455403 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE6C_hz89 hx hc) (lowGroupedE6C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (10559774375455403 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (10559774375455403 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE6C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE6C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE6C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE6C_hz94 hx hc) (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE6C_hz96 hx hc) (lowGroupedE6C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE6C_hz97 hx hc) (lowGroupedE6C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE6C_hz98 hx hc) (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE6C_hz95 hx hc) (lowGroupedE6C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE6C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (1751301202510343 / 40000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE6C_hz93 hx hc) (lowGroupedE6C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (45659464724802979 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE6C_hz100 hx hc) (lowGroupedE6C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (69757185386478253 / 100000000000000000) (93721765771200671 / 125000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE6C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (89378383946298579 / 125000000000000000) (186541217660758513 / 250000000000000000) ((neb x (kdot (156327257 / 250000000)/2+√23*x))^2) := bsq (lowGroupedE6C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE6C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE6C_hz106 hx hc) (lowGroupedE6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (89378383946298579 / 125000000000000000) (373240090327453091 / 500000000000000000) (((neb x (kdot (156327257 / 250000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE6C_hz105 hx hc) (lowGroupedE6C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (498782759878862537 / 1000000000000000000) (139922881288365359 / 250000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (156327257 / 250000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE6C_hz104 hx hc) (lowGroupedE6C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (498782759878862537 / 1000000000000000000) (121070197975652883 / 200000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (156327257 / 250000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE6C_hz103 hx hc) (lowGroupedE6C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE6C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) : B (498782759878862537 / 1000000000000000000) (121070197975652883 / 200000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (156327257 / 250000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE6C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE6C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (458426349 / 1000000000) (156327257 / 250000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (156327257 / 250000000)/2+√23*x)^2) (np1 x) ≤ (60535099 / 100000000) :=
  (lowGroupedE6C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE8W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE8W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (38220573 / 100000000) (146342409 / 200000000) c := hc

theorem lowGroupedE8W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE8W_hz2 hx hc) (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE8W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE8W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE8W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE8W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE8W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE8W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE8W_hz11 hx hc) (lowGroupedE8W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE8W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE8W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (312417715937654969 / 500000000000000000) (78104428993189167 / 125000000000000000) (kdot ((38220573 / 100000000))) := by
    constructor
    · apply bkdot_lower (q := (167138154363348271 / 250000000000000000)) (a := (294653562776928453 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (668552617453393083 / 1000000000000000000)) (a := (147326781360895417 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE8W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (1460812200448329 / 10000000000000000) (1460812200448329 / 10000000000000000) (((38220573 / 100000000) : ℝ)^2) := bsq (bpoint ((38220573 / 100000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (8539187799551671 / 10000000000000000) (8539187799551671 / 10000000000000000) ((1 : ℝ) - (((38220573 / 100000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE8W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (924077258650577927 / 1000000000000000000) (115509657331322241 / 125000000000000000) (√((1 : ℝ) - (((38220573 / 100000000) : ℝ)^2))) := bsqrt (lowGroupedE8W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (294142927026094753 / 1000000000000000000) (58828585405218951 / 200000000000000000) ((√((1 : ℝ) - (((38220573 / 100000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE8W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (238815682369768103 / 1000000000000000000) (47763136479320049 / 200000000000000000) (((38220573 / 100000000) : ℝ) * (kdot ((38220573 / 100000000)))) := bmul (bpoint ((38220573 / 100000000) : ℝ)) (lowGroupedE8W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (66619826174482857 / 125000000000000000) (106591721884539 / 200000000000000) (((√((1 : ℝ) - (((38220573 / 100000000) : ℝ)^2))) / Real.pi) + (((38220573 / 100000000) : ℝ) * (kdot ((38220573 / 100000000))))) := badd (lowGroupedE8W_hz18 hx hc) (lowGroupedE8W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (66619826174482857 / 125000000000000000) (106591721884539 / 200000000000000) (kappa ((38220573 / 100000000))) := by rw [kappa_eq]; exact (lowGroupedE8W_hz20 hx hc)

theorem lowGroupedE8W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (23789950258952517 / 31250000000000000) (761278408286480547 / 1000000000000000000) (kdot ((146342409 / 200000000))) := by
    constructor
    · apply bkdot_lower (q := (78721388268157957 / 200000000000000000)) (a := (374982999390227391 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (49200867667598723 / 125000000000000000)) (a := (374982999390227389 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE8W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (21416100671923281 / 40000000000000000) (21416100671923281 / 40000000000000000) (((146342409 / 200000000) : ℝ)^2) := bsq (bpoint ((146342409 / 200000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (18583899328076719 / 40000000000000000) (18583899328076719 / 40000000000000000) ((1 : ℝ) - (((146342409 / 200000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE8W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (681613881315454119 / 1000000000000000000) (17040347032886353 / 25000000000000000) (√((1 : ℝ) - (((146342409 / 200000000) : ℝ)^2))) := bsqrt (lowGroupedE8W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (216964436982814003 / 1000000000000000000) (54241109245703501 / 250000000000000000) ((√((1 : ℝ) - (((146342409 / 200000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE8W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (69629572617705703 / 125000000000000000) (557036580941645627 / 1000000000000000000) (((146342409 / 200000000) : ℝ) * (kdot ((146342409 / 200000000)))) := bmul (bpoint ((146342409 / 200000000) : ℝ)) (lowGroupedE8W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (774001017924459627 / 1000000000000000000) (774001017924459631 / 1000000000000000000) (((√((1 : ℝ) - (((146342409 / 200000000) : ℝ)^2))) / Real.pi) + (((146342409 / 200000000) : ℝ) * (kdot ((146342409 / 200000000))))) := badd (lowGroupedE8W_hz26 hx hc) (lowGroupedE8W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (774001017924459627 / 1000000000000000000) (774001017924459631 / 1000000000000000000) (kappa ((146342409 / 200000000))) := by rw [kappa_eq]; exact (lowGroupedE8W_hz28 hx hc)

theorem lowGroupedE8W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (66619826174482857 / 125000000000000000) (774001017924459631 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE8W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE8W_hz21 hx hc).1 (lowGroupedE8W_hz29 hx hc).2

theorem lowGroupedE8W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (225998982075540369 / 1000000000000000000) (58380173825517143 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE8W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (225998982075540369 / 500000000000000000) (58380173825517143 / 62500000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE8W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (225998919575540369 / 500000000000000000) (58380173825517143 / 62500000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE8W_hz32 hx hc) (lowGroupedE8W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (336153922761240709 / 500000000000000000) (483239790685813219 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE8W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE8W_hz36 hx hc) (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (668916680530918783 / 1000000000000000000) (483239790685813219 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE8W_hz35 hx hc) (lowGroupedE8W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (668916680530918783 / 1000000000000000000) (483239790685813219 / 500000000000000000) (ndm x c) := by
    convert (lowGroupedE8W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE8W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE8W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE8W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (447449525492503259 / 1000000000000000000) (93408278120827429 / 100000000000000000) ((ndm x c)^2) := bsq (lowGroupedE8W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (106591721879172571 / 100000000000000000) (311867710898124403 / 200000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE8W_hz41 hx hc) (lowGroupedE8W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE8W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE8W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (106591721879172571 / 200000000000000000) (24447500899220521 / 31250000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE8W_hz43 hx hc) (lowGroupedE8W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (106591721879172571 / 200000000000000000) (24447500899220521 / 31250000000000000) (nc1 x c) := by
    convert (lowGroupedE8W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE8W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (84864982614005833 / 125000000000000000) (169729965228013133 / 250000000000000000) (kdot ((106591721879172571 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (551966183095358367 / 1000000000000000000)) (a := (63043937885768951 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (275983091547679183 / 500000000000000000)) (a := (504351503086142391 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE8W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (785963825656627123 / 1000000000000000000) (6287710605253017 / 8000000000000000) (kdot ((24447500899220521 / 31250000000000000))) := by
    constructor
    · apply bkdot_lower (q := (174737612003992571 / 500000000000000000)) (a := (10506476139368819 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (349475224007985141 / 1000000000000000000)) (a := (168103618229901103 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE8W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (84864982614005833 / 125000000000000000) (6287710605253017 / 8000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE8W_hz47 hx hc) (lowGroupedE8W_hz48 hx hc).1 (lowGroupedE8W_hz49 hx hc).2

theorem lowGroupedE8W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE8W_hz51 hx hc) (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE8W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (84864982614005833 / 250000000000000000) (392981912828313563 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE8W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (84864982614005833 / 250000000000000000) (393581391768727653 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE8W_hz54 hx hc) (lowGroupedE8W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (23789950258952517 / 62500000000000000) (190319602071620137 / 500000000000000000) ((kdot ((146342409 / 200000000))) / (2 : ℝ)) := bdiv (lowGroupedE8W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (23789950258952517 / 62500000000000000) (95309670770913591 / 250000000000000000) (((kdot ((146342409 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE8W_hz56 hx hc) (lowGroupedE8W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE8W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE8W_hz58 hx hc) (lowGroupedE8W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE8W_hz3 hx hc) (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE8W_hz60 hx hc) (lowGroupedE8W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE8W_hz4 hx hc) (lowGroupedE8W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE8W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE8W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (308479822736933749 / 500000000000000000) (77180660940303559 / 125000000000000000) (√(((kdot ((146342409 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE8W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (308479822736933749 / 500000000000000000) (628625627409927421 / 1000000000000000000) ((√(((kdot ((146342409 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE8W_hz65 hx hc) (lowGroupedE8W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (308479822736933749 / 500000000000000000) (629824585290755601 / 1000000000000000000) (((√(((kdot ((146342409 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE8W_hz66 hx hc) (lowGroupedE8W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (10906408725825499 / 12500000000000000) (890706470434196719 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((146342409 / 200000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE8W_hz4 hx hc) (lowGroupedE8W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (10906408725825499 / 12500000000000000) (890706470434196719 / 1000000000000000000) (neb x (kdot (146342409 / 200000000)/2+√23*x)) := by
    convert (lowGroupedE8W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE8W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE8W_hz4 hx hc) (lowGroupedE8W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE8W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE8W_hz3 hx hc) (lowGroupedE8W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE8W_hz71 hx hc) (lowGroupedE8W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE8W_hz4 hx hc) (lowGroupedE8W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE8W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE8W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE8W_hz4 hx hc) (lowGroupedE8W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE8W_hz76 hx hc) (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE8W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE8W_hz4 hx hc) (lowGroupedE8W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE8W_hz79 hx hc) (lowGroupedE8W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE8W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE8W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE8W_hz70 hx hc) (lowGroupedE8W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE8W_hz82 hx hc) (lowGroupedE8W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE8W_hz4 hx hc) (lowGroupedE8W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE8W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE8W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (29131594981052073 / 50000000000000000) (156840163815093863 / 250000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE8W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (29131594981052073 / 25000000000000000) (156840163815093863 / 125000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE8W_hz70 hx hc) (lowGroupedE8W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (5335810963369183 / 250000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE8W_hz87 hx hc) (lowGroupedE8W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE8W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (2163259573069699 / 100000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE8W_hz89 hx hc) (lowGroupedE8W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (2163259573069699 / 50000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (2163259573069699 / 50000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE8W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE8W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE8W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE8W_hz94 hx hc) (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE8W_hz96 hx hc) (lowGroupedE8W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE8W_hz97 hx hc) (lowGroupedE8W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE8W_hz98 hx hc) (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE8W_hz95 hx hc) (lowGroupedE8W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE8W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (8969223576558639 / 200000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE8W_hz93 hx hc) (lowGroupedE8W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (46723052544837599 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE8W_hz100 hx hc) (lowGroupedE8W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (84864982614005833 / 125000000000000000) (393581391768727653 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (761278408286480541 / 1000000000000000000) (396679008236672277 / 500000000000000000) ((neb x (kdot (146342409 / 200000000)/2+√23*x))^2) := bsq (lowGroupedE8W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE8W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE8W_hz106 hx hc) (lowGroupedE8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (761278408286480541 / 1000000000000000000) (198418331621304171 / 250000000000000000) (((neb x (kdot (146342409 / 200000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE8W_hz105 hx hc) (lowGroupedE8W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (516847031069201641 / 1000000000000000000) (312375052447767357 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (146342409 / 200000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE8W_hz104 hx hc) (lowGroupedE8W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (516847031069201641 / 1000000000000000000) (671473157440372313 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (146342409 / 200000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE8W_hz103 hx hc) (lowGroupedE8W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) : B (516847031069201641 / 1000000000000000000) (671473157440372313 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (146342409 / 200000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE8W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE8W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (38220573 / 100000000) (146342409 / 200000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (146342409 / 200000000)/2+√23*x)^2) (np1 x) ≤ (335736579 / 500000000) :=
  (lowGroupedE8W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE8C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE8C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (457416159 / 1000000000) (15608373 / 25000000) c := hc

theorem lowGroupedE8C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE8C_hz2 hx hc) (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE8C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE8C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE8C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE8C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE8C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE8C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE8C_hz11 hx hc) (lowGroupedE8C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE8C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE8C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (40701563276327303 / 62500000000000000) (32561250621101683 / 50000000000000000) (kdot ((457416159 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (122031411112831361 / 200000000000000000)) (a := (136963617341664213 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (152539263891039201 / 250000000000000000)) (a := (21914178774616209 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE8C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (209229542514313281 / 1000000000000000000) (209229542514313281 / 1000000000000000000) (((457416159 / 1000000000) : ℝ)^2) := bsq (bpoint ((457416159 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (790770457485686719 / 1000000000000000000) (790770457485686719 / 1000000000000000000) ((1 : ℝ) - (((457416159 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE8C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (222313188076765747 / 250000000000000000) (889252752307062989 / 1000000000000000000) (√((1 : ℝ) - (((457416159 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE8C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (283057942375483817 / 1000000000000000000) (141528971187741909 / 500000000000000000) ((√((1 : ℝ) - (((457416159 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE8C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (297880843826449449 / 1000000000000000000) (74470210956703481 / 250000000000000000) (((457416159 / 1000000000) : ℝ) * (kdot ((457416159 / 1000000000)))) := bmul (bpoint ((457416159 / 1000000000) : ℝ)) (lowGroupedE8C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (290469393100966633 / 500000000000000000) (290469393101148871 / 500000000000000000) (((√((1 : ℝ) - (((457416159 / 1000000000) : ℝ)^2))) / Real.pi) + (((457416159 / 1000000000) : ℝ) * (kdot ((457416159 / 1000000000))))) := badd (lowGroupedE8C_hz18 hx hc) (lowGroupedE8C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (290469393100966633 / 500000000000000000) (290469393101148871 / 500000000000000000) (kappa ((457416159 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE8C_hz20 hx hc)

theorem lowGroupedE8C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (714629938795140177 / 1000000000000000000) (714629938795140187 / 1000000000000000000) (kdot ((15608373 / 25000000))) := by
    constructor
    · apply bkdot_lower (q := (480908688059088679 / 1000000000000000000)) (a := (448258243917828639 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (240454344029544339 / 500000000000000000)) (a := (224129121958914313 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE8C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (243621307707129 / 625000000000000) (243621307707129 / 625000000000000) (((15608373 / 25000000) : ℝ)^2) := bsq (bpoint ((15608373 / 25000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (381378692292871 / 625000000000000) (381378692292871 / 625000000000000) ((1 : ℝ) - (((15608373 / 25000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE8C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (781156775345764763 / 1000000000000000000) (195289193836441191 / 250000000000000000) (√((1 : ℝ) - (((15608373 / 25000000) : ℝ)^2))) := bsqrt (lowGroupedE8C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (6216248106300183 / 25000000000000000) (248649924252007321 / 1000000000000000000) ((√((1 : ℝ) - (((15608373 / 25000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE8C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (223084212833634369 / 500000000000000000) (223084212833634373 / 500000000000000000) (((15608373 / 25000000) : ℝ) * (kdot ((15608373 / 25000000)))) := bmul (bpoint ((15608373 / 25000000) : ℝ)) (lowGroupedE8C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (347409174959638029 / 500000000000000000) (694818349919276067 / 1000000000000000000) (((√((1 : ℝ) - (((15608373 / 25000000) : ℝ)^2))) / Real.pi) + (((15608373 / 25000000) : ℝ) * (kdot ((15608373 / 25000000))))) := badd (lowGroupedE8C_hz26 hx hc) (lowGroupedE8C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (347409174959638029 / 500000000000000000) (694818349919276067 / 1000000000000000000) (kappa ((15608373 / 25000000))) := by rw [kappa_eq]; exact (lowGroupedE8C_hz28 hx hc)

theorem lowGroupedE8C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (290469393100966633 / 500000000000000000) (694818349919276067 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE8C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE8C_hz21 hx hc).1 (lowGroupedE8C_hz29 hx hc).2

theorem lowGroupedE8C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (305181650080723933 / 1000000000000000000) (209530606899033367 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE8C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (305181650080723933 / 500000000000000000) (209530606899033367 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE8C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (305181587580723933 / 500000000000000000) (209530606899033367 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE8C_hz32 hx hc) (lowGroupedE8C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (195314358016993957 / 250000000000000000) (915490266248709751 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE8C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE8C_hz36 hx hc) (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (777866267076413193 / 1000000000000000000) (915490266248709751 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE8C_hz35 hx hc) (lowGroupedE8C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (777866267076413193 / 1000000000000000000) (915490266248709751 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE8C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE8C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE8C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE8C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (605075929455393779 / 1000000000000000000) (838122427596133469 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE8C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (1161877572403866531 / 1000000000000000000) (280342430105546299 / 200000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE8C_hz41 hx hc) (lowGroupedE8C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE8C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE8C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (116187757240386653 / 200000000000000000) (351619437221385151 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE8C_hz43 hx hc) (lowGroupedE8C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (116187757240386653 / 200000000000000000) (351619437221385151 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE8C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE8C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (348657219392471757 / 500000000000000000) (69731443878494371 / 100000000000000000) (kdot ((116187757240386653 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (514850579705586043 / 1000000000000000000)) (a := (475457367730462553 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (257425289852793021 / 500000000000000000)) (a := (475457367730462247 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE8C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (748263557914328227 / 1000000000000000000) (748263557914328229 / 1000000000000000000) (kdot ((351619437221385151 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (104353190818083139 / 250000000000000000)) (a := (98856669637147361 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (83482552654466511 / 200000000000000000)) (a := (197713339274294721 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE8C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (348657219392471757 / 500000000000000000) (748263557914328229 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE8C_hz47 hx hc) (lowGroupedE8C_hz48 hx hc).1 (lowGroupedE8C_hz49 hx hc).2

theorem lowGroupedE8C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE8C_hz51 hx hc) (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE8C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (348657219392471757 / 1000000000000000000) (74826355791432823 / 200000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE8C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (348657219392471757 / 1000000000000000000) (74946251579515641 / 200000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE8C_hz54 hx hc) (lowGroupedE8C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (44664371174696261 / 125000000000000000) (178657484698785047 / 500000000000000000) ((kdot ((15608373 / 25000000))) / (2 : ℝ)) := bdiv (lowGroupedE8C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (44664371174696261 / 125000000000000000) (44739306042248023 / 125000000000000000) (((kdot ((15608373 / 25000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE8C_hz56 hx hc) (lowGroupedE8C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE8C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE8C_hz58 hx hc) (lowGroupedE8C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE8C_hz3 hx hc) (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE8C_hz60 hx hc) (lowGroupedE8C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE8C_hz4 hx hc) (lowGroupedE8C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE8C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE8C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (298879143383061311 / 500000000000000000) (299129757938751467 / 500000000000000000) (√(((kdot ((15608373 / 25000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE8C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (298879143383061311 / 500000000000000000) (609439855765001883 / 1000000000000000000) ((√(((kdot ((15608373 / 25000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE8C_hz65 hx hc) (lowGroupedE8C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (298879143383061311 / 500000000000000000) (610638813645830063 / 1000000000000000000) (((√(((kdot ((15608373 / 25000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE8C_hz66 hx hc) (lowGroupedE8C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (84535787616555639 / 100000000000000000) (431786845984674929 / 500000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((15608373 / 25000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE8C_hz4 hx hc) (lowGroupedE8C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (84535787616555639 / 100000000000000000) (431786845984674929 / 500000000000000000) (neb x (kdot (15608373 / 25000000)/2+√23*x)) := by
    convert (lowGroupedE8C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE8C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE8C_hz4 hx hc) (lowGroupedE8C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE8C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE8C_hz3 hx hc) (lowGroupedE8C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE8C_hz71 hx hc) (lowGroupedE8C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE8C_hz4 hx hc) (lowGroupedE8C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE8C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE8C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE8C_hz4 hx hc) (lowGroupedE8C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE8C_hz76 hx hc) (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE8C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE8C_hz4 hx hc) (lowGroupedE8C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE8C_hz79 hx hc) (lowGroupedE8C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE8C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE8C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE8C_hz70 hx hc) (lowGroupedE8C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE8C_hz82 hx hc) (lowGroupedE8C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE8C_hz4 hx hc) (lowGroupedE8C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE8C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE8C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (59047203099932833 / 100000000000000000) (153038242340268133 / 250000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE8C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (59047203099932833 / 50000000000000000) (153038242340268133 / 125000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE8C_hz70 hx hc) (lowGroupedE8C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (20825867849938241 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE8C_hz87 hx hc) (lowGroupedE8C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE8C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (21115219727158499 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE8C_hz89 hx hc) (lowGroupedE8C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (21115219727158499 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (21115219727158499 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE8C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE8C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE8C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE8C_hz94 hx hc) (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE8C_hz96 hx hc) (lowGroupedE8C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE8C_hz97 hx hc) (lowGroupedE8C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE8C_hz98 hx hc) (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE8C_hz95 hx hc) (lowGroupedE8C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE8C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (43773555646931173 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE8C_hz93 hx hc) (lowGroupedE8C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (45650490308975577 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE8C_hz100 hx hc) (lowGroupedE8C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (348657219392471757 / 500000000000000000) (74946251579515641 / 100000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE8C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (178657484698785043 / 250000000000000000) (46609970091348347 / 62500000000000000) ((neb x (kdot (15608373 / 25000000)/2+√23*x))^2) := bsq (lowGroupedE8C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE8C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE8C_hz106 hx hc) (lowGroupedE8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (178657484698785043 / 250000000000000000) (373037415736722841 / 500000000000000000) (((neb x (kdot (15608373 / 25000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE8C_hz105 hx hc) (lowGroupedE8C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (498321774709851701 / 1000000000000000000) (279577560083767971 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (15608373 / 25000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE8C_hz104 hx hc) (lowGroupedE8C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (498321774709851701 / 1000000000000000000) (604805610476511519 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (15608373 / 25000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE8C_hz103 hx hc) (lowGroupedE8C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE8C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) : B (498321774709851701 / 1000000000000000000) (604805610476511519 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (15608373 / 25000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE8C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE8C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (457416159 / 1000000000) (15608373 / 25000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (15608373 / 25000000)/2+√23*x)^2) (np1 x) ≤ (604805611 / 1000000000) :=
  (lowGroupedE8C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE10W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE10W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (381181879 / 1000000000) (730796277 / 1000000000) c := hc

theorem lowGroupedE10W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE10W_hz2 hx hc) (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE10W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE10W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE10W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE10W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE10W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE10W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE10W_hz11 hx hc) (lowGroupedE10W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE10W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE10W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (78060354298177873 / 125000000000000000) (624482834459872477 / 1000000000000000000) (kdot ((381181879 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (33467716371266747 / 50000000000000000)) (a := (294930492197904217 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (669354327425334939 / 1000000000000000000)) (a := (117972196855772689 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE10W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (145299624877970641 / 1000000000000000000) (145299624877970641 / 1000000000000000000) (((381181879 / 1000000000) : ℝ)^2) := bsq (bpoint ((381181879 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (854700375122029359 / 1000000000000000000) (854700375122029359 / 1000000000000000000) ((1 : ℝ) - (((381181879 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE10W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (924500067670105343 / 1000000000000000000) (3611328389336349 / 3906250000000000) (√((1 : ℝ) - (((381181879 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE10W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (58855502263395601 / 200000000000000000) (147138755658489003 / 500000000000000000) ((√((1 : ℝ) - (((381181879 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE10W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (238041540214281343 / 1000000000000000000) (238041540242660141 / 1000000000000000000) (((381181879 / 1000000000) : ℝ) * (kdot ((381181879 / 1000000000)))) := bmul (bpoint ((381181879 / 1000000000) : ℝ)) (lowGroupedE10W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (133079762882814837 / 250000000000000000) (532319051559638147 / 1000000000000000000) (((√((1 : ℝ) - (((381181879 / 1000000000) : ℝ)^2))) / Real.pi) + (((381181879 / 1000000000) : ℝ) * (kdot ((381181879 / 1000000000))))) := badd (lowGroupedE10W_hz18 hx hc) (lowGroupedE10W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (133079762882814837 / 250000000000000000) (532319051559638147 / 1000000000000000000) (kappa ((381181879 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE10W_hz20 hx hc)

theorem lowGroupedE10W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (76085105755994539 / 100000000000000000) (760851057559945393 / 1000000000000000000) (kdot ((730796277 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (394382426465596321 / 1000000000000000000)) (a := (375654280341721941 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (2464890165409977 / 6250000000000000)) (a := (375654280341721939 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE10W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (534063198477060729 / 1000000000000000000) (534063198477060729 / 1000000000000000000) (((730796277 / 1000000000) : ℝ)^2) := bsq (bpoint ((730796277 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (465936801522939271 / 1000000000000000000) (465936801522939271 / 1000000000000000000) ((1 : ℝ) - (((730796277 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE10W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (682595635440880379 / 1000000000000000000) (34129781772044019 / 50000000000000000) (√((1 : ℝ) - (((730796277 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE10W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (217276939026738903 / 1000000000000000000) (27159617378342363 / 125000000000000000) ((√((1 : ℝ) - (((730796277 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE10W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (111205424043264159 / 200000000000000000) (278013560108160399 / 500000000000000000) (((730796277 / 1000000000) : ℝ) * (kdot ((730796277 / 1000000000)))) := bmul (bpoint ((730796277 / 1000000000) : ℝ)) (lowGroupedE10W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (386652029621529849 / 500000000000000000) (386652029621529851 / 500000000000000000) (((√((1 : ℝ) - (((730796277 / 1000000000) : ℝ)^2))) / Real.pi) + (((730796277 / 1000000000) : ℝ) * (kdot ((730796277 / 1000000000))))) := badd (lowGroupedE10W_hz26 hx hc) (lowGroupedE10W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (386652029621529849 / 500000000000000000) (386652029621529851 / 500000000000000000) (kappa ((730796277 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE10W_hz28 hx hc)

theorem lowGroupedE10W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (133079762882814837 / 250000000000000000) (386652029621529851 / 500000000000000000) (kappa c) := bkappa (lowGroupedE10W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE10W_hz21 hx hc).1 (lowGroupedE10W_hz29 hx hc).2

theorem lowGroupedE10W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (113347970378470149 / 500000000000000000) (116920237117185163 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE10W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (113347970378470149 / 250000000000000000) (116920237117185163 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE10W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (113347939128470149 / 250000000000000000) (116920237117185163 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE10W_hz32 hx hc) (lowGroupedE10W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (336671856751451901 / 500000000000000000) (967141094637944389 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE10W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE10W_hz36 hx hc) (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (669952548511341167 / 1000000000000000000) (967141094637944389 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE10W_hz35 hx hc) (lowGroupedE10W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (669952548511341167 / 1000000000000000000) (967141094637944389 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE10W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE10W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE10W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE10W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (448836417256840939 / 1000000000000000000) (187072379387496261 / 200000000000000000) ((ndm x c)^2) := bsq (lowGroupedE10W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (212927620612503739 / 200000000000000000) (311590332545256867 / 200000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE10W_hz41 hx hc) (lowGroupedE10W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE10W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE10W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (532319051531259347 / 1000000000000000000) (390812112643593399 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE10W_hz43 hx hc) (lowGroupedE10W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (532319051531259347 / 1000000000000000000) (390812112643593399 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE10W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE10W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (678679322871822323 / 1000000000000000000) (135735864574365691 / 200000000000000000) (kdot ((532319051531259347 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (276229618166842753 / 500000000000000000)) (a := (100945867871238089 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (110491847266737101 / 200000000000000000)) (a := (100945867871236163 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE10W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (392804248433951183 / 500000000000000000) (785608496867902369 / 1000000000000000000) (kdot ((390812112643593399 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (87525415953780567 / 250000000000000000)) (a := (21047836600995971 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (350101663815122267 / 1000000000000000000)) (a := (168382692807967767 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE10W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (678679322871822323 / 1000000000000000000) (785608496867902369 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE10W_hz47 hx hc) (lowGroupedE10W_hz48 hx hc).1 (lowGroupedE10W_hz49 hx hc).2

theorem lowGroupedE10W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE10W_hz51 hx hc) (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE10W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (339339661435911161 / 1000000000000000000) (78560849686790237 / 200000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE10W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (339339661435911161 / 1000000000000000000) (15736149094974611 / 40000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE10W_hz54 hx hc) (lowGroupedE10W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (76085105755994539 / 200000000000000000) (380425528779972697 / 1000000000000000000) ((kdot ((730796277 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE10W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (76085105755994539 / 200000000000000000) (381025007720386787 / 1000000000000000000) (((kdot ((730796277 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE10W_hz56 hx hc) (lowGroupedE10W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE10W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE10W_hz58 hx hc) (lowGroupedE10W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE10W_hz3 hx hc) (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE10W_hz60 hx hc) (lowGroupedE10W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE10W_hz4 hx hc) (lowGroupedE10W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE10W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE10W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (38549153321399529 / 62500000000000000) (154318057862727699 / 250000000000000000) (√(((kdot ((730796277 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE10W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (38549153321399529 / 62500000000000000) (125690514267681949 / 200000000000000000) ((√(((kdot ((730796277 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE10W_hz65 hx hc) (lowGroupedE10W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (38549153321399529 / 62500000000000000) (25186061168769517 / 40000000000000000) (((√(((kdot ((730796277 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE10W_hz66 hx hc) (lowGroupedE10W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (872267767121968911 / 1000000000000000000) (890461732190805413 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((730796277 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE10W_hz4 hx hc) (lowGroupedE10W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (872267767121968911 / 1000000000000000000) (890461732190805413 / 1000000000000000000) (neb x (kdot (730796277 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE10W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE10W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE10W_hz4 hx hc) (lowGroupedE10W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE10W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE10W_hz3 hx hc) (lowGroupedE10W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE10W_hz71 hx hc) (lowGroupedE10W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE10W_hz4 hx hc) (lowGroupedE10W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE10W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE10W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE10W_hz4 hx hc) (lowGroupedE10W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE10W_hz76 hx hc) (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE10W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE10W_hz4 hx hc) (lowGroupedE10W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE10W_hz79 hx hc) (lowGroupedE10W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE10W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE10W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE10W_hz70 hx hc) (lowGroupedE10W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE10W_hz82 hx hc) (lowGroupedE10W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE10W_hz4 hx hc) (lowGroupedE10W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE10W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE10W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (582528678638151823 / 1000000000000000000) (125443808515903291 / 200000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE10W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (582528678638151823 / 500000000000000000) (125443808515903291 / 100000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE10W_hz70 hx hc) (lowGroupedE10W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (266730326150331 / 12500000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE10W_hz87 hx hc) (lowGroupedE10W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE10W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (10813888984623369 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE10W_hz89 hx hc) (lowGroupedE10W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (10813888984623369 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (10813888984623369 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE10W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE10W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE10W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE10W_hz94 hx hc) (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE10W_hz96 hx hc) (lowGroupedE10W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE10W_hz97 hx hc) (lowGroupedE10W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE10W_hz98 hx hc) (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE10W_hz95 hx hc) (lowGroupedE10W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE10W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (22418065137125051 / 500000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE10W_hz93 hx hc) (lowGroupedE10W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (23356532468147253 / 500000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE10W_hz100 hx hc) (lowGroupedE10W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (339339661435911161 / 500000000000000000) (15736149094974611 / 20000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (190212764389986347 / 250000000000000000) (396461048248124831 / 500000000000000000) ((neb x (kdot (730796277 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE10W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE10W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE10W_hz106 hx hc) (lowGroupedE10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (190212764389986347 / 250000000000000000) (12394334476689403 / 15625000000000000) (((neb x (kdot (730796277 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE10W_hz105 hx hc) (lowGroupedE10W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (103274776110218729 / 200000000000000000) (312062552413069709 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (730796277 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE10W_hz104 hx hc) (lowGroupedE10W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (103274776110218729 / 200000000000000000) (167709542440608481 / 250000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (730796277 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE10W_hz103 hx hc) (lowGroupedE10W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) : B (103274776110218729 / 200000000000000000) (167709542440608481 / 250000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (730796277 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE10W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE10W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (381181879 / 1000000000) (730796277 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (730796277 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (67083817 / 100000000) :=
  (lowGroupedE10W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE10C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE10C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (228203139 / 500000000) (9740007 / 15625000) c := hc

theorem lowGroupedE10C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE10C_hz2 hx hc) (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE10C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE10C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE10C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE10C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE10C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE10C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE10C_hz11 hx hc) (lowGroupedE10C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE10C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE10C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (650863628845345861 / 1000000000000000000) (40678976802887131 / 62500000000000000) (kdot ((228203139 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (24437452824588471 / 40000000000000000)) (a := (27421106468011521 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (305468160307355887 / 500000000000000000)) (a := (548422129358898017 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE10C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (52076672649453321 / 250000000000000000) (52076672649453321 / 250000000000000000) (((228203139 / 500000000) : ℝ)^2) := bsq (bpoint ((228203139 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (197923327350546679 / 250000000000000000) (197923327350546679 / 250000000000000000) ((1 : ℝ) - (((228203139 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE10C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (889771492801487047 / 1000000000000000000) (111221436600185881 / 125000000000000000) (√((1 : ℝ) - (((228203139 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE10C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (141611531301611431 / 500000000000000000) (17701441412701429 / 62500000000000000) ((√((1 : ℝ) - (((228203139 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE10C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (148529123163438871 / 500000000000000000) (148529123163632441 / 500000000000000000) (((228203139 / 500000000) : ℝ) * (kdot ((228203139 / 500000000)))) := bmul (bpoint ((228203139 / 500000000) : ℝ)) (lowGroupedE10C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (145070327232525151 / 250000000000000000) (290140654465243873 / 500000000000000000) (((√((1 : ℝ) - (((228203139 / 500000000) : ℝ)^2))) / Real.pi) + (((228203139 / 500000000) : ℝ) * (kdot ((228203139 / 500000000))))) := badd (lowGroupedE10C_hz18 hx hc) (lowGroupedE10C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (145070327232525151 / 250000000000000000) (290140654465243873 / 500000000000000000) (kappa ((228203139 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE10C_hz20 hx hc)

theorem lowGroupedE10C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (178558263363454127 / 250000000000000000) (357116526726908259 / 500000000000000000) (kdot ((9740007 / 15625000))) := by
    constructor
    · apply bkdot_lower (q := (60209565764313533 / 125000000000000000)) (a := (448881669954138597 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (481676526114508263 / 1000000000000000000)) (a := (56110208744267323 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE10C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (94867736360049 / 244140625000000) (94867736360049 / 244140625000000) (((9740007 / 15625000) : ℝ)^2) := bsq (bpoint ((9740007 / 15625000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (149272888639951 / 244140625000000) (149272888639951 / 244140625000000) ((1 : ℝ) - (((9740007 / 15625000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE10C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (781934621224331833 / 1000000000000000000) (390967310612165917 / 500000000000000000) (√((1 : ℝ) - (((9740007 / 15625000) : ℝ)^2))) := bsqrt (lowGroupedE10C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (49779504057016507 / 200000000000000000) (31112190035635317 / 125000000000000000) ((√((1 : ℝ) - (((9740007 / 15625000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE10C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (89044927235475801 / 200000000000000000) (111306159044344753 / 250000000000000000) (((9740007 / 15625000) : ℝ) * (kdot ((9740007 / 15625000)))) := bmul (bpoint ((9740007 / 15625000) : ℝ)) (lowGroupedE10C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (34706107823123077 / 50000000000000000) (173530539115615387 / 250000000000000000) (((√((1 : ℝ) - (((9740007 / 15625000) : ℝ)^2))) / Real.pi) + (((9740007 / 15625000) : ℝ) * (kdot ((9740007 / 15625000))))) := badd (lowGroupedE10C_hz26 hx hc) (lowGroupedE10C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (34706107823123077 / 50000000000000000) (173530539115615387 / 250000000000000000) (kappa ((9740007 / 15625000))) := by rw [kappa_eq]; exact (lowGroupedE10C_hz28 hx hc)

theorem lowGroupedE10C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (145070327232525151 / 250000000000000000) (173530539115615387 / 250000000000000000) (kappa c) := bkappa (lowGroupedE10C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE10C_hz21 hx hc).1 (lowGroupedE10C_hz29 hx hc).2

theorem lowGroupedE10C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (76469460884384613 / 250000000000000000) (104929672767474849 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE10C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (76469460884384613 / 125000000000000000) (104929672767474849 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE10C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (76469445259384613 / 125000000000000000) (104929672767474849 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE10C_hz32 hx hc) (lowGroupedE10C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (391074021789698051 / 500000000000000000) (229052038593279987 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE10C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE10C_hz36 hx hc) (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (778756878587833467 / 1000000000000000000) (229052038593279987 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE10C_hz35 hx hc) (lowGroupedE10C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (778756878587833467 / 1000000000000000000) (229052038593279987 / 250000000000000000) (ndm x c) := by
    convert (lowGroupedE10C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE10C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE10C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE10C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (121292455189573119 / 200000000000000000) (419718691069899397 / 500000000000000000) ((ndm x c)^2) := bsq (lowGroupedE10C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (580281308930100603 / 500000000000000000) (1400325804035259679 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE10C_hz41 hx hc) (lowGroupedE10C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE10C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE10C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (580281308930100603 / 1000000000000000000) (702543344517752167 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE10C_hz43 hx hc) (lowGroupedE10C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (580281308930100603 / 1000000000000000000) (702543344517752167 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE10C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE10C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (697057393571224749 / 1000000000000000000) (348528696785612477 / 500000000000000000) (kdot ((580281308930100603 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (257680739118039307 / 500000000000000000)) (a := (237930566703996099 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (515361478236078613 / 1000000000000000000)) (a := (475861133407991877 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE10C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (46747019003100647 / 62500000000000000) (373976152024805177 / 500000000000000000) (kdot ((702543344517752167 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (417986982510890639 / 1000000000000000000)) (a := (197957797487994499 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (208993491255445319 / 500000000000000000)) (a := (395915594975988997 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE10C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (697057393571224749 / 1000000000000000000) (373976152024805177 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE10C_hz47 hx hc) (lowGroupedE10C_hz48 hx hc).1 (lowGroupedE10C_hz49 hx hc).2

theorem lowGroupedE10C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE10C_hz51 hx hc) (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE10C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (174264348392806187 / 500000000000000000) (373976152024805177 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE10C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (174264348392806187 / 500000000000000000) (374575630965219267 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE10C_hz54 hx hc) (lowGroupedE10C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (178558263363454127 / 500000000000000000) (357116526726908259 / 1000000000000000000) ((kdot ((9740007 / 15625000))) / (2 : ℝ)) := bdiv (lowGroupedE10C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (178558263363454127 / 500000000000000000) (357716005667322349 / 1000000000000000000) (((kdot ((9740007 / 15625000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE10C_hz56 hx hc) (lowGroupedE10C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE10C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE10C_hz58 hx hc) (lowGroupedE10C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE10C_hz3 hx hc) (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE10C_hz60 hx hc) (lowGroupedE10C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE10C_hz4 hx hc) (lowGroupedE10C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE10C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE10C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (597592274654641309 / 1000000000000000000) (149523410722895319 / 250000000000000000) (√(((kdot ((9740007 / 15625000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE10C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (597592274654641309 / 1000000000000000000) (24370959311163209 / 40000000000000000) ((√(((kdot ((9740007 / 15625000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE10C_hz65 hx hc) (lowGroupedE10C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (597592274654641309 / 1000000000000000000) (122094588131981681 / 200000000000000000) (((√(((kdot ((9740007 / 15625000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE10C_hz66 hx hc) (lowGroupedE10C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (845123099585981323 / 1000000000000000000) (26979347254469629 / 31250000000000000) ((√(2 : ℝ)) * (((√(((kdot ((9740007 / 15625000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE10C_hz4 hx hc) (lowGroupedE10C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (845123099585981323 / 1000000000000000000) (26979347254469629 / 31250000000000000) (neb x (kdot (9740007 / 15625000)/2+√23*x)) := by
    convert (lowGroupedE10C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE10C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE10C_hz4 hx hc) (lowGroupedE10C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE10C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE10C_hz3 hx hc) (lowGroupedE10C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE10C_hz71 hx hc) (lowGroupedE10C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE10C_hz4 hx hc) (lowGroupedE10C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE10C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE10C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE10C_hz4 hx hc) (lowGroupedE10C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE10C_hz76 hx hc) (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE10C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE10C_hz4 hx hc) (lowGroupedE10C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE10C_hz79 hx hc) (lowGroupedE10C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE10C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE10C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE10C_hz70 hx hc) (lowGroupedE10C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE10C_hz82 hx hc) (lowGroupedE10C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE10C_hz4 hx hc) (lowGroupedE10C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE10C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE10C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (147590797643690419 / 250000000000000000) (306012920873130481 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE10C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (147590797643690419 / 125000000000000000) (306012920873130481 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE10C_hz70 hx hc) (lowGroupedE10C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (5205385720115963 / 250000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE10C_hz87 hx hc) (lowGroupedE10C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE10C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (2111089475768411 / 100000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE10C_hz89 hx hc) (lowGroupedE10C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (2111089475768411 / 50000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (2111089475768411 / 50000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE10C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE10C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE10C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE10C_hz94 hx hc) (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE10C_hz96 hx hc) (lowGroupedE10C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE10C_hz97 hx hc) (lowGroupedE10C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE10C_hz98 hx hc) (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE10C_hz95 hx hc) (lowGroupedE10C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE10C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (2735286852246831 / 62500000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE10C_hz93 hx hc) (lowGroupedE10C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (456415242979937 / 10000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE10C_hz100 hx hc) (lowGroupedE10C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (174264348392806187 / 250000000000000000) (374575630965219267 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE10C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (89279131681727063 / 125000000000000000) (745354422555912099 / 1000000000000000000) ((neb x (kdot (9740007 / 15625000)/2+√23*x))^2) := bsq (lowGroupedE10C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE10C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE10C_hz106 hx hc) (lowGroupedE10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (89279131681727063 / 125000000000000000) (745669732567784229 / 1000000000000000000) (((neb x (kdot (9740007 / 15625000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE10C_hz105 hx hc) (lowGroupedE10C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (248930715321467287 / 500000000000000000) (34913713821030511 / 62500000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (9740007 / 15625000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE10C_hz104 hx hc) (lowGroupedE10C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (248930715321467287 / 500000000000000000) (151065236358620469 / 250000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (9740007 / 15625000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE10C_hz103 hx hc) (lowGroupedE10C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE10C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) : B (248930715321467287 / 500000000000000000) (151065236358620469 / 250000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (9740007 / 15625000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE10C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE10C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (228203139 / 500000000) (9740007 / 15625000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (9740007 / 15625000)/2+√23*x)^2) (np1 x) ≤ (302130473 / 500000000) :=
  (lowGroupedE10C_hz111 hx hc).2.trans (by norm_num)

end BstLean.BlueprintLow
