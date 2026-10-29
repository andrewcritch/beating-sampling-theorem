import BstLean.Part264bNormalize
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
open BstLean.Part264b
theorem lowCoarseS32_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS32_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (31 / 50) (63 / 100) c := hc

theorem lowCoarseS32_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS32_hz2 hx hc) (lowCoarseS32_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS32_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS32_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS32_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS32_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS32_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS32_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS32_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS32_hz10 hx hc) (lowCoarseS32_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS32_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS32_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (11138553339727929 / 15625000000000000) (712867413742587469 / 1000000000000000000) (kdot ((31 / 50))) := by
    constructor
    · apply bkdot_lower (q := (484322104837852617 / 1000000000000000000)) (a := (90205362359252487 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (60540263104731577 / 125000000000000000)) (a := (451026811796262417 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS32_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (961 / 2500) (961 / 2500) (((31 / 50) : ℝ)^2) := bsq (bpoint ((31 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (1539 / 2500) (1539 / 2500) ((1 : ℝ) - (((31 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS32_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (784601809837321239 / 1000000000000000000) (19615045245933031 / 25000000000000000) (√((1 : ℝ) - (((31 / 50) : ℝ)^2))) := bsqrt (lowCoarseS32_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (49949302557782779 / 200000000000000000) (31218314098614237 / 125000000000000000) ((√((1 : ℝ) - (((31 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS32_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (220988898260202111 / 500000000000000000) (441977796520404231 / 1000000000000000000) (((31 / 50) : ℝ) * (kdot ((31 / 50)))) := bmul (bpoint ((31 / 50) : ℝ)) (lowCoarseS32_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (691724309309318117 / 1000000000000000000) (691724309309318127 / 1000000000000000000) (((√((1 : ℝ) - (((31 / 50) : ℝ)^2))) / Real.pi) + (((31 / 50) : ℝ) * (kdot ((31 / 50))))) := badd (lowCoarseS32_hz17 hx hc) (lowCoarseS32_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (691724309309318117 / 1000000000000000000) (691724309309318127 / 1000000000000000000) (kappa ((31 / 50))) := by rw [kappa_eq]; exact (lowCoarseS32_hz19 hx hc)

theorem lowCoarseS32_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (716945125200852751 / 1000000000000000000) (716945125200852757 / 1000000000000000000) (kdot ((63 / 100))) := by
    constructor
    · apply bkdot_lower (q := (119109682916281739 / 250000000000000000)) (a := (444621557615889849 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (95287746333025391 / 200000000000000000)) (a := (444621557615889841 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS32_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (3969 / 10000) (3969 / 10000) (((63 / 100) : ℝ)^2) := bsq (bpoint ((63 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (6031 / 10000) (6031 / 10000) ((1 : ℝ) - (((63 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS32_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (776595132614156937 / 1000000000000000000) (388297566307078469 / 500000000000000000) (√((1 : ℝ) - (((63 / 100) : ℝ)^2))) := bsqrt (lowCoarseS32_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (247197908273298117 / 1000000000000000000) (123598954136649059 / 500000000000000000) ((√((1 : ℝ) - (((63 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS32_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (451675428876537233 / 1000000000000000000) (451675428876537237 / 1000000000000000000) (((63 / 100) : ℝ) * (kdot ((63 / 100)))) := bmul (bpoint ((63 / 100) : ℝ)) (lowCoarseS32_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (13977466742996707 / 20000000000000000) (139774667429967071 / 200000000000000000) (((√((1 : ℝ) - (((63 / 100) : ℝ)^2))) / Real.pi) + (((63 / 100) : ℝ) * (kdot ((63 / 100))))) := badd (lowCoarseS32_hz25 hx hc) (lowCoarseS32_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (13977466742996707 / 20000000000000000) (139774667429967071 / 200000000000000000) (kappa ((63 / 100))) := by rw [kappa_eq]; exact (lowCoarseS32_hz27 hx hc)

theorem lowCoarseS32_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (691724309309318117 / 1000000000000000000) (139774667429967071 / 200000000000000000) (kappa c) := bkappa (lowCoarseS32_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS32_hz20 hx hc).1 (lowCoarseS32_hz28 hx hc).2

theorem lowCoarseS32_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (60225332570032929 / 200000000000000000) (308275690690681883 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS32_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (60225332570032929 / 100000000000000000) (308275690690681883 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS32_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS32_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (60225320070032929 / 100000000000000000) (308275690690681883 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS32_hz31 hx hc) (lowCoarseS32_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (776049741125096497 / 1000000000000000000) (392603929355452251 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS32_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS32_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS32_hz35 hx hc) (lowCoarseS32_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (386329288066766931 / 500000000000000000) (392603929355452251 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS32_hz34 hx hc) (lowCoarseS32_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (386329288066766931 / 500000000000000000) (392603929355452251 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS32_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS32_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS32_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS32_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (597001275272699943 / 1000000000000000000) (77068922672670471 / 125000000000000000) ((ndm x c)^2) := bsq (lowCoarseS32_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (172931077327329529 / 125000000000000000) (1409786804710425331 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS32_hz40 hx hc) (lowCoarseS32_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS32_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS32_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (172931077327329529 / 250000000000000000) (17682248195101433 / 25000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS32_hz42 hx hc) (lowCoarseS32_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (172931077327329529 / 250000000000000000) (17682248195101433 / 25000000000000000) (nc1 x c) := by
    convert (lowCoarseS32_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS32_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (11138553339727929 / 15625000000000000) (716945125200852757 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS32_hz1 hx hc) (lowCoarseS32_hz13 hx hc).1 (lowCoarseS32_hz21 hx hc).2

theorem lowCoarseS32_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (743148657518033877 / 1000000000000000000) (743148657518033879 / 1000000000000000000) (kdot ((172931077327329529 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (106719763322825347 / 250000000000000000)) (a := (40346114530301037 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (426879053291301387 / 1000000000000000000)) (a := (403461145303010369 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS32_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (4688015347654081 / 6250000000000000) (750082455624652963 / 1000000000000000000) (kdot ((17682248195101433 / 25000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (414061827231350567 / 1000000000000000000)) (a := (78513912141279141 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (207030913615675283 / 500000000000000000)) (a := (392569560706395703 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS32_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (743148657518033877 / 1000000000000000000) (750082455624652963 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS32_hz46 hx hc) (lowCoarseS32_hz48 hx hc).1 (lowCoarseS32_hz49 hx hc).2

theorem lowCoarseS32_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (961 / 2500) (3969 / 10000) (c^2) := bsq (lowCoarseS32_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (6031 / 10000) (1539 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS32_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (776595132614156937 / 1000000000000000000) (19615045245933031 / 25000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS32_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (276804681855867893 / 500000000000000000) (562516442786633943 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS32_hz53 hx hc) (lowCoarseS32_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (276804681855867893 / 500000000000000000) (562516442786633943 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS32_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS32_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (247197908273298117 / 1000000000000000000) (31218314098614237 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS32_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (220988898260202111 / 500000000000000000) (451675428876537237 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS32_hz1 hx hc) (lowCoarseS32_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-2555969007540489 / 12500000000000000) (-96115641865745163 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS32_hz56 hx hc) (lowCoarseS32_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-2555969007540489 / 12500000000000000) (-96115641865745163 / 500000000000000000) (npp c) := by
    convert (lowCoarseS32_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS32_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS32_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS32_hz3 hx hc) (lowCoarseS32_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS32_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS32_hz62 hx hc) (lowCoarseS32_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS32_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS32_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS32_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS32_hz65 hx hc) (lowCoarseS32_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS32_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS32_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS32_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS32_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (276804681855867893 / 500000000000000000) (288456281178286051 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS32_hz55 hx hc) (lowCoarseS32_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (276804681855867893 / 500000000000000000) (288946217842266303 / 500000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS32_hz69 hx hc) (lowCoarseS32_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (276804681855867893 / 500000000000000000) (144897004545078481 / 250000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS32_hz70 hx hc) (lowCoarseS32_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (276804681855867893 / 500000000000000000) (144897004545078481 / 250000000000000000) (nlam x c) := by
    convert (lowCoarseS32_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS32_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS32_hz73 hx hc) (lowCoarseS32_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS32_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS32_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS32_hz3 hx hc) (lowCoarseS32_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS32_hz76 hx hc) (lowCoarseS32_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS32_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS32_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS32_hz80 hx hc) (lowCoarseS32_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS32_hz81 hx hc) (lowCoarseS32_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS32_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS32_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-2555969007540489 / 12500000000000000) (-91316935342432443 / 500000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS32_hz59 hx hc) (lowCoarseS32_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-15337500077411817 / 100000000000000000) (-91316935342432443 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS32_hz84 hx hc) (lowCoarseS32_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (306483327589312959 / 1000000000000000000) (10497570963068247 / 31250000000000000) ((nlam x c)^2) := bsq (lowCoarseS32_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (478482520089453201 / 1000000000000000000) (62532380246633577 / 125000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS32_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (62467619753366423 / 125000000000000000) (521517479910546799 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS32_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (706923587120228563 / 1000000000000000000) (722161671587842441 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS32_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (277608243493281779 / 125000000000000000) (283592225270561341 / 125000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS32_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (27017959263244289 / 200000000000000000) (4726791805140637 / 31250000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS32_hz86 hx hc) (lowCoarseS32_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-731408178315869 / 40000000000000000) (59940402422067941 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS32_hz85 hx hc) (lowCoarseS32_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS32_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-731408178315869 / 40000000000000000) (29971638711033971 / 500000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS32_hz92 hx hc) (lowCoarseS32_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-731408178315869 / 40000000000000000) (16191008536688539 / 250000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS32_hz94 hx hc) (lowCoarseS32_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-731408178315869 / 40000000000000000) (16191008536688539 / 250000000000000000) (nu x c) := by
    convert (lowCoarseS32_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS32_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-2675936670623307 / 12500000000000000) (-96115641865745163 / 500000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS32_hz59 hx hc) (lowCoarseS32_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-2675936670623307 / 12500000000000000) (-96115641865745163 / 500000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS32_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-80286925959887531 / 500000000000000000) (-142856420438025301 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS32_hz50 hx hc) (lowCoarseS32_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-160576726919775063 / 1000000000000000000) (-142856420438025301 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS32_hz99 hx hc) (lowCoarseS32_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-165397483644461277 / 1000000000000000000) (-142856420438025301 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS32_hz100 hx hc) (lowCoarseS32_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B (-165397483644461277 / 1000000000000000000) (-142856420438025301 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS32_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS32_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (16191008536688539 / 250000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS32_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (165397483644461277 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS32_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (165397483644461277 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS32_hz103 hx hc) (lowCoarseS32_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS32_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) : B 0 (165397483644461277 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS32_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS32 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (31 / 50) (63 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS32_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS32_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS32_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS32_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS32_hz38 hx hc).1) (lowCoarseS32_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS32_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS32_hz55 hx hc).1,(lowCoarseS32_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS32_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS32_hz68 hx hc).2 (lowCoarseS32_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS32_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS32_hz55 hx hc).1,(lowCoarseS32_hz64 hx hc).2]

theorem lowCoarseS33_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS33_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (63 / 100) (16 / 25) c := hc

theorem lowCoarseS33_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS33_hz2 hx hc) (lowCoarseS33_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS33_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS33_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS33_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS33_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS33_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS33_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS33_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS33_hz10 hx hc) (lowCoarseS33_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS33_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS33_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (716945125200852751 / 1000000000000000000) (716945125200852757 / 1000000000000000000) (kdot ((63 / 100))) := by
    constructor
    · apply bkdot_lower (q := (119109682916281739 / 250000000000000000)) (a := (444621557615889849 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (95287746333025391 / 200000000000000000)) (a := (444621557615889841 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS33_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (3969 / 10000) (3969 / 10000) (((63 / 100) : ℝ)^2) := bsq (bpoint ((63 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (6031 / 10000) (6031 / 10000) ((1 : ℝ) - (((63 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS33_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (776595132614156937 / 1000000000000000000) (388297566307078469 / 500000000000000000) (√((1 : ℝ) - (((63 / 100) : ℝ)^2))) := bsqrt (lowCoarseS33_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (247197908273298117 / 1000000000000000000) (123598954136649059 / 500000000000000000) ((√((1 : ℝ) - (((63 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS33_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (451675428876537233 / 1000000000000000000) (451675428876537237 / 1000000000000000000) (((63 / 100) : ℝ) * (kdot ((63 / 100)))) := bmul (bpoint ((63 / 100) : ℝ)) (lowCoarseS33_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (13977466742996707 / 20000000000000000) (139774667429967071 / 200000000000000000) (((√((1 : ℝ) - (((63 / 100) : ℝ)^2))) / Real.pi) + (((63 / 100) : ℝ) * (kdot ((63 / 100))))) := badd (lowCoarseS33_hz17 hx hc) (lowCoarseS33_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (13977466742996707 / 20000000000000000) (139774667429967071 / 200000000000000000) (kappa ((63 / 100))) := by rw [kappa_eq]; exact (lowCoarseS33_hz19 hx hc)

theorem lowCoarseS33_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (5633325499112727 / 7812500000000000) (721065663886429061 / 1000000000000000000) (kdot ((16 / 25))) := by
    constructor
    · apply bkdot_lower (q := (468521285665818197 / 1000000000000000000)) (a := (438149030584170317 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (117130321416454549 / 250000000000000000)) (a := (54768628823021289 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS33_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (256 / 625) (256 / 625) (((16 / 25) : ℝ)^2) := bsq (bpoint ((16 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (369 / 625) (369 / 625) ((1 : ℝ) - (((16 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS33_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (384187454245970921 / 500000000000000000) (768374908491941843 / 1000000000000000000) (√((1 : ℝ) - (((16 / 25) : ℝ)^2))) := bsqrt (lowCoarseS33_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (12229066483427529 / 50000000000000000) (244581329668550581 / 1000000000000000000) ((√((1 : ℝ) - (((16 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS33_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (92296404977462919 / 200000000000000000) (2307410124436573 / 5000000000000000) (((16 / 25) : ℝ) * (kdot ((16 / 25)))) := bmul (bpoint ((16 / 25) : ℝ)) (lowCoarseS33_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (28242534182234607 / 40000000000000000) (706063354555865181 / 1000000000000000000) (((√((1 : ℝ) - (((16 / 25) : ℝ)^2))) / Real.pi) + (((16 / 25) : ℝ) * (kdot ((16 / 25))))) := badd (lowCoarseS33_hz25 hx hc) (lowCoarseS33_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (28242534182234607 / 40000000000000000) (706063354555865181 / 1000000000000000000) (kappa ((16 / 25))) := by rw [kappa_eq]; exact (lowCoarseS33_hz27 hx hc)

theorem lowCoarseS33_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (13977466742996707 / 20000000000000000) (706063354555865181 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS33_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS33_hz20 hx hc).1 (lowCoarseS33_hz28 hx hc).2

theorem lowCoarseS33_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (293936645444134819 / 1000000000000000000) (6022533257003293 / 20000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS33_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (293936645444134819 / 500000000000000000) (6022533257003293 / 10000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS33_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS33_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (293936582944134819 / 500000000000000000) (6022533257003293 / 10000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS33_hz31 hx hc) (lowCoarseS33_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (766728873780210287 / 1000000000000000000) (388024910830583563 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS33_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS33_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS33_hz35 hx hc) (lowCoarseS33_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (190834427197161913 / 250000000000000000) (388024910830583563 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS33_hz34 hx hc) (lowCoarseS33_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (190834427197161913 / 250000000000000000) (388024910830583563 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS33_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS33_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS33_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS33_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (291342228829351123 / 500000000000000000) (301126662850164651 / 500000000000000000) ((ndm x c)^2) := bsq (lowCoarseS33_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (698873337149835349 / 500000000000000000) (356025905581105757 / 250000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS33_hz40 hx hc) (lowCoarseS33_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS33_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS33_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (698873337149835349 / 1000000000000000000) (357236337031197729 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS33_hz42 hx hc) (lowCoarseS33_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (698873337149835349 / 1000000000000000000) (357236337031197729 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS33_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS33_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (716945125200852751 / 1000000000000000000) (721065663886429061 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS33_hz1 hx hc) (lowCoarseS33_hz13 hx hc).1 (lowCoarseS33_hz21 hx hc).2

theorem lowCoarseS33_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (746314896832702841 / 1000000000000000000) (746314896832702843 / 1000000000000000000) (kdot ((698873337149835349 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (421011642108715549 / 1000000000000000000)) (a := (398487628217774771 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (105252910527178887 / 250000000000000000)) (a := (398487628217774769 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS33_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (47083333174943237 / 62500000000000000) (150666666159818359 / 200000000000000000) (kdot ((357236337031197729 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (51011555680255153 / 125000000000000000)) (a := (387463097923518469 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (408092445442041223 / 1000000000000000000)) (a := (387463097923518467 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS33_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (746314896832702841 / 1000000000000000000) (150666666159818359 / 200000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS33_hz46 hx hc) (lowCoarseS33_hz48 hx hc).1 (lowCoarseS33_hz49 hx hc).2

theorem lowCoarseS33_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (3969 / 10000) (256 / 625) (c^2) := bsq (lowCoarseS33_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (369 / 625) (6031 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS33_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (384187454245970921 / 500000000000000000) (388297566307078469 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS33_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (550882644969949019 / 1000000000000000000) (55997608486939649 / 100000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS33_hz53 hx hc) (lowCoarseS33_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (550882644969949019 / 1000000000000000000) (55997608486939649 / 100000000000000000) (npa c) := by
    convert (lowCoarseS33_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS33_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (12229066483427529 / 50000000000000000) (123598954136649059 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS33_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (451675428876537233 / 1000000000000000000) (2307410124436573 / 5000000000000000) (c * (kdot c)) := bmul (lowCoarseS33_hz1 hx hc) (lowCoarseS33_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-10845034760938201 / 50000000000000000) (-40895504120647823 / 200000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS33_hz56 hx hc) (lowCoarseS33_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-10845034760938201 / 50000000000000000) (-40895504120647823 / 200000000000000000) (npp c) := by
    convert (lowCoarseS33_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS33_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS33_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS33_hz3 hx hc) (lowCoarseS33_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS33_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS33_hz62 hx hc) (lowCoarseS33_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS33_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS33_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS33_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS33_hz65 hx hc) (lowCoarseS33_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS33_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS33_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS33_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS33_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (550882644969949019 / 1000000000000000000) (574372204439334649 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS33_hz55 hx hc) (lowCoarseS33_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (550882644969949019 / 1000000000000000000) (287673881512557921 / 500000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS33_hz69 hx hc) (lowCoarseS33_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (550882644969949019 / 1000000000000000000) (14426083638022429 / 25000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS33_hz70 hx hc) (lowCoarseS33_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (550882644969949019 / 1000000000000000000) (14426083638022429 / 25000000000000000) (nlam x c) := by
    convert (lowCoarseS33_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS33_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS33_hz73 hx hc) (lowCoarseS33_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS33_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS33_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS33_hz3 hx hc) (lowCoarseS33_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS33_hz76 hx hc) (lowCoarseS33_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS33_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS33_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS33_hz80 hx hc) (lowCoarseS33_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS33_hz81 hx hc) (lowCoarseS33_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS33_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS33_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-10845034760938201 / 50000000000000000) (-7795204302264547 / 40000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS33_hz59 hx hc) (lowCoarseS33_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-2553101924715471 / 15625000000000000) (-97440053778306837 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS33_hz84 hx hc) (lowCoarseS33_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (303471688529086897 / 1000000000000000000) (66595804521989901 / 200000000000000000) ((nlam x c)^2) := bsq (lowCoarseS33_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (488423941378947429 / 1000000000000000000) (63808900247733747 / 125000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS33_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (61191099752266253 / 125000000000000000) (511576058621052571 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS33_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (349831673100839321 / 500000000000000000) (22351420419005179 / 31250000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS33_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (549514307103311447 / 250000000000000000) (1123504930970297097 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS33_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (135055788436548479 / 1000000000000000000) (37871969199173619 / 250000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS33_hz86 hx hc) (lowCoarseS33_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-5668546949048333 / 200000000000000000) (54047823018387639 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS33_hz85 hx hc) (lowCoarseS33_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS33_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-5668546949048333 / 200000000000000000) (1351267450459691 / 25000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS33_hz92 hx hc) (lowCoarseS33_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-5668546949048333 / 200000000000000000) (29435727371536927 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS33_hz94 hx hc) (lowCoarseS33_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-5668546949048333 / 200000000000000000) (29435727371536927 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS33_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS33_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-11324905413269473 / 50000000000000000) (-40895504120647823 / 200000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS33_hz59 hx hc) (lowCoarseS33_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-11324905413269473 / 50000000000000000) (-40895504120647823 / 200000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS33_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-85314287159629573 / 500000000000000000) (-152604619693613269 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS33_hz50 hx hc) (lowCoarseS33_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-170631449319259147 / 1000000000000000000) (-152604619693613269 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS33_hz99 hx hc) (lowCoarseS33_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-175452206043945361 / 1000000000000000000) (-152604619693613269 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS33_hz100 hx hc) (lowCoarseS33_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B (-175452206043945361 / 1000000000000000000) (-152604619693613269 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS33_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS33_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (29435727371536927 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS33_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (175452206043945361 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS33_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (175452206043945361 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS33_hz103 hx hc) (lowCoarseS33_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS33_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) : B 0 (175452206043945361 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS33_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS33 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (63 / 100) (16 / 25) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS33_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS33_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS33_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS33_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS33_hz38 hx hc).1) (lowCoarseS33_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS33_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS33_hz55 hx hc).1,(lowCoarseS33_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS33_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS33_hz68 hx hc).2 (lowCoarseS33_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS33_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS33_hz55 hx hc).1,(lowCoarseS33_hz64 hx hc).2]

theorem lowCoarseS34_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS34_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (16 / 25) (13 / 20) c := hc

theorem lowCoarseS34_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS34_hz2 hx hc) (lowCoarseS34_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS34_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS34_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS34_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS34_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS34_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS34_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS34_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS34_hz10 hx hc) (lowCoarseS34_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS34_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS34_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (5633325499112727 / 7812500000000000) (721065663886429061 / 1000000000000000000) (kdot ((16 / 25))) := by
    constructor
    · apply bkdot_lower (q := (468521285665818197 / 1000000000000000000)) (a := (438149030584170317 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (117130321416454549 / 250000000000000000)) (a := (54768628823021289 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS34_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (256 / 625) (256 / 625) (((16 / 25) : ℝ)^2) := bsq (bpoint ((16 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (369 / 625) (369 / 625) ((1 : ℝ) - (((16 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS34_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (384187454245970921 / 500000000000000000) (768374908491941843 / 1000000000000000000) (√((1 : ℝ) - (((16 / 25) : ℝ)^2))) := bsqrt (lowCoarseS34_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (12229066483427529 / 50000000000000000) (244581329668550581 / 1000000000000000000) ((√((1 : ℝ) - (((16 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS34_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (92296404977462919 / 200000000000000000) (2307410124436573 / 5000000000000000) (((16 / 25) : ℝ) * (kdot ((16 / 25)))) := bmul (bpoint ((16 / 25) : ℝ)) (lowCoarseS34_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (28242534182234607 / 40000000000000000) (706063354555865181 / 1000000000000000000) (((√((1 : ℝ) - (((16 / 25) : ℝ)^2))) / Real.pi) + (((16 / 25) : ℝ) * (kdot ((16 / 25))))) := badd (lowCoarseS34_hz17 hx hc) (lowCoarseS34_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (28242534182234607 / 40000000000000000) (706063354555865181 / 1000000000000000000) (kappa ((16 / 25))) := by rw [kappa_eq]; exact (lowCoarseS34_hz19 hx hc)

theorem lowCoarseS34_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (181307780379867391 / 250000000000000000) (708233517108857 / 976562500000000) (kdot ((13 / 20))) := by
    constructor
    · apply bkdot_lower (q := (115141546617959573 / 250000000000000000)) (a := (431605945034770523 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (460566186471838291 / 1000000000000000000)) (a := (431605945034770519 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS34_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (169 / 400) (169 / 400) (((13 / 20) : ℝ)^2) := bsq (bpoint ((13 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (231 / 400) (231 / 400) ((1 : ℝ) - (((13 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS34_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (759934207678533181 / 1000000000000000000) (379967103839266591 / 500000000000000000) (√((1 : ℝ) - (((13 / 20) : ℝ)^2))) := bsqrt (lowCoarseS34_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (241894571153323039 / 1000000000000000000) (241894571153323041 / 1000000000000000000) ((√((1 : ℝ) - (((13 / 20) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS34_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (29462514311728451 / 62500000000000000) (23570011449382761 / 50000000000000000) (((13 / 20) : ℝ) * (kdot ((13 / 20)))) := bmul (bpoint ((13 / 20) : ℝ)) (lowCoarseS34_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (142658960028195651 / 200000000000000000) (713294800140978261 / 1000000000000000000) (((√((1 : ℝ) - (((13 / 20) : ℝ)^2))) / Real.pi) + (((13 / 20) : ℝ) * (kdot ((13 / 20))))) := badd (lowCoarseS34_hz25 hx hc) (lowCoarseS34_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (142658960028195651 / 200000000000000000) (713294800140978261 / 1000000000000000000) (kappa ((13 / 20))) := by rw [kappa_eq]; exact (lowCoarseS34_hz27 hx hc)

theorem lowCoarseS34_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (28242534182234607 / 40000000000000000) (713294800140978261 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS34_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS34_hz20 hx hc).1 (lowCoarseS34_hz28 hx hc).2

theorem lowCoarseS34_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (286705199859021739 / 1000000000000000000) (11757465817765393 / 40000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS34_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (286705199859021739 / 500000000000000000) (11757465817765393 / 20000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS34_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS34_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (286705137359021739 / 500000000000000000) (11757465817765393 / 20000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS34_hz31 hx hc) (lowCoarseS34_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (378619292534745077 / 500000000000000000) (766728955295330979 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS34_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS34_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS34_hz35 hx hc) (lowCoarseS34_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (753847420077927519 / 1000000000000000000) (766728955295330979 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS34_hz34 hx hc) (lowCoarseS34_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (753847420077927519 / 1000000000000000000) (766728955295330979 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS34_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS34_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS34_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS34_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (284142966379073659 / 500000000000000000) (587873290888269651 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS34_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (1412126709111730349 / 1000000000000000000) (359625536806244489 / 250000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS34_hz40 hx hc) (lowCoarseS34_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS34_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS34_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (353031677277932587 / 500000000000000000) (721696412859901247 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS34_hz42 hx hc) (lowCoarseS34_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (353031677277932587 / 500000000000000000) (721696412859901247 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS34_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS34_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (5633325499112727 / 7812500000000000) (708233517108857 / 976562500000000) (kdot c) := bkdot (lowCoarseS34_hz1 hx hc) (lowCoarseS34_hz13 hx hc).1 (lowCoarseS34_hz21 hx hc).2

theorem lowCoarseS34_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (149906127773185177 / 200000000000000000) (749530638865925887 / 1000000000000000000) (kdot ((353031677277932587 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (415077592800739667 / 1000000000000000000)) (a := (393436352444068061 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (207538796400369833 / 500000000000000000)) (a := (393436352444068059 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS34_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (1477807265766347 / 1953125000000000) (756637320072369667 / 1000000000000000000) (kdot ((721696412859901247 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (16082038818810089 / 40000000000000000)) (a := (47784150463660481 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (6282046413597691 / 15625000000000000)) (a := (191136601854641923 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS34_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (149906127773185177 / 200000000000000000) (756637320072369667 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS34_hz46 hx hc) (lowCoarseS34_hz48 hx hc).1 (lowCoarseS34_hz49 hx hc).2

theorem lowCoarseS34_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (256 / 625) (169 / 400) (c^2) := bsq (lowCoarseS34_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (231 / 400) (369 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS34_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (759934207678533181 / 1000000000000000000) (768374908491941843 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS34_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (547962463969728981 / 1000000000000000000) (111449879326606157 / 200000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS34_hz53 hx hc) (lowCoarseS34_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (547962463969728981 / 1000000000000000000) (111449879326606157 / 200000000000000000) (npa c) := by
    convert (lowCoarseS34_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS34_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (241894571153323039 / 1000000000000000000) (244581329668550581 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS34_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (92296404977462919 / 200000000000000000) (23570011449382761 / 50000000000000000) (c * (kdot c)) := bmul (lowCoarseS34_hz1 hx hc) (lowCoarseS34_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-229505657834332181 / 1000000000000000000) (-108450347609382007 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS34_hz56 hx hc) (lowCoarseS34_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-229505657834332181 / 1000000000000000000) (-108450347609382007 / 500000000000000000) (npp c) := by
    convert (lowCoarseS34_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS34_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS34_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS34_hz3 hx hc) (lowCoarseS34_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS34_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS34_hz62 hx hc) (lowCoarseS34_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS34_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS34_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS34_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS34_hz65 hx hc) (lowCoarseS34_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS34_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS34_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS34_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS34_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (547962463969728981 / 1000000000000000000) (35727844762685559 / 62500000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS34_hz55 hx hc) (lowCoarseS34_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (547962463969728981 / 1000000000000000000) (143154110892153109 / 250000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS34_hz69 hx hc) (lowCoarseS34_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (547962463969728981 / 1000000000000000000) (287156013032196877 / 500000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS34_hz70 hx hc) (lowCoarseS34_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (547962463969728981 / 1000000000000000000) (287156013032196877 / 500000000000000000) (nlam x c) := by
    convert (lowCoarseS34_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS34_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS34_hz73 hx hc) (lowCoarseS34_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS34_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS34_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS34_hz3 hx hc) (lowCoarseS34_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS34_hz76 hx hc) (lowCoarseS34_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS34_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS34_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS34_hz80 hx hc) (lowCoarseS34_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS34_hz81 hx hc) (lowCoarseS34_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS34_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS34_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-229505657834332181 / 1000000000000000000) (-103651641086069287 / 500000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS34_hz59 hx hc) (lowCoarseS34_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-86826272942607677 / 500000000000000000) (-103651641086069287 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS34_hz84 hx hc) (lowCoarseS34_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (300262861919776531 / 1000000000000000000) (329834303282188891 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS34_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (249262730323340687 / 500000000000000000) (104169142466969807 / 200000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS34_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (95830857533030193 / 200000000000000000) (250737269676659313 / 500000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS34_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (692209713645475337 / 1000000000000000000) (708148670374603349 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS34_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (1087320475566059887 / 500000000000000000) (2224714660498233937 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS34_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (67483454676504769 / 500000000000000000) (30334598740125527 / 200000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS34_hz86 hx hc) (lowCoarseS34_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-4835704566525727 / 125000000000000000) (12005338153639587 / 250000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS34_hz85 hx hc) (lowCoarseS34_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS34_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-4835704566525727 / 125000000000000000) (48024227614558349 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS34_hz92 hx hc) (lowCoarseS34_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-4835704566525727 / 125000000000000000) (52844984339244563 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS34_hz94 hx hc) (lowCoarseS34_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-4835704566525727 / 125000000000000000) (52844984339244563 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS34_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS34_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-239103070880957621 / 1000000000000000000) (-108450347609382007 / 500000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS34_hz59 hx hc) (lowCoarseS34_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-239103070880957621 / 1000000000000000000) (-108450347609382007 / 500000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS34_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-22614288346555203 / 125000000000000000) (-162573716657783667 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS34_hz50 hx hc) (lowCoarseS34_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-1447337454179533 / 8000000000000000) (-162573716657783667 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS34_hz99 hx hc) (lowCoarseS34_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-185737938497127839 / 1000000000000000000) (-162573716657783667 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS34_hz100 hx hc) (lowCoarseS34_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B (-185737938497127839 / 1000000000000000000) (-162573716657783667 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS34_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS34_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (52844984339244563 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS34_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (185737938497127839 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS34_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (185737938497127839 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS34_hz103 hx hc) (lowCoarseS34_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS34_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) : B 0 (185737938497127839 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS34_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS34 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (16 / 25) (13 / 20) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS34_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS34_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS34_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS34_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS34_hz38 hx hc).1) (lowCoarseS34_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS34_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS34_hz55 hx hc).1,(lowCoarseS34_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS34_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS34_hz68 hx hc).2 (lowCoarseS34_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS34_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS34_hz55 hx hc).1,(lowCoarseS34_hz64 hx hc).2]

theorem lowCoarseS35_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS35_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (13 / 20) (33 / 50) c := hc

theorem lowCoarseS35_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS35_hz2 hx hc) (lowCoarseS35_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS35_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS35_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS35_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS35_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS35_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS35_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS35_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS35_hz10 hx hc) (lowCoarseS35_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS35_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS35_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (181307780379867391 / 250000000000000000) (708233517108857 / 976562500000000) (kdot ((13 / 20))) := by
    constructor
    · apply bkdot_lower (q := (115141546617959573 / 250000000000000000)) (a := (431605945034770523 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (460566186471838291 / 1000000000000000000)) (a := (431605945034770519 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS35_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (169 / 400) (169 / 400) (((13 / 20) : ℝ)^2) := bsq (bpoint ((13 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (231 / 400) (231 / 400) ((1 : ℝ) - (((13 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS35_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (759934207678533181 / 1000000000000000000) (379967103839266591 / 500000000000000000) (√((1 : ℝ) - (((13 / 20) : ℝ)^2))) := bsqrt (lowCoarseS35_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (241894571153323039 / 1000000000000000000) (241894571153323041 / 1000000000000000000) ((√((1 : ℝ) - (((13 / 20) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS35_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (29462514311728451 / 62500000000000000) (23570011449382761 / 50000000000000000) (((13 / 20) : ℝ) * (kdot ((13 / 20)))) := bmul (bpoint ((13 / 20) : ℝ)) (lowCoarseS35_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (142658960028195651 / 200000000000000000) (713294800140978261 / 1000000000000000000) (((√((1 : ℝ) - (((13 / 20) : ℝ)^2))) / Real.pi) + (((13 / 20) : ℝ) * (kdot ((13 / 20))))) := badd (lowCoarseS35_hz17 hx hc) (lowCoarseS35_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (142658960028195651 / 200000000000000000) (713294800140978261 / 1000000000000000000) (kappa ((13 / 20))) := by rw [kappa_eq]; exact (lowCoarseS35_hz19 hx hc)

theorem lowCoarseS35_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (364721868865849627 / 500000000000000000) (729443737731699257 / 1000000000000000000) (kdot ((33 / 50))) := by
    constructor
    · apply bkdot_lower (q := (452569637855251769 / 1000000000000000000)) (a := (84997756592480699 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56571204731906471 / 125000000000000000)) (a := (424988782962403493 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS35_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (1089 / 2500) (1089 / 2500) (((33 / 50) : ℝ)^2) := bsq (bpoint ((33 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (1411 / 2500) (1411 / 2500) ((1 : ℝ) - (((33 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS35_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (46954099927482371 / 62500000000000000) (751265598839717937 / 1000000000000000000) (√((1 : ℝ) - (((33 / 50) : ℝ)^2))) := bsqrt (lowCoarseS35_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (239135267260467957 / 1000000000000000000) (119567633630233979 / 500000000000000000) ((√((1 : ℝ) - (((33 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS35_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (481432866902921507 / 1000000000000000000) (48143286690292151 / 100000000000000000) (((33 / 50) : ℝ) * (kdot ((33 / 50)))) := bmul (bpoint ((33 / 50) : ℝ)) (lowCoarseS35_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (90071016770423683 / 125000000000000000) (180142033540847367 / 250000000000000000) (((√((1 : ℝ) - (((33 / 50) : ℝ)^2))) / Real.pi) + (((33 / 50) : ℝ) * (kdot ((33 / 50))))) := badd (lowCoarseS35_hz25 hx hc) (lowCoarseS35_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (90071016770423683 / 125000000000000000) (180142033540847367 / 250000000000000000) (kappa ((33 / 50))) := by rw [kappa_eq]; exact (lowCoarseS35_hz27 hx hc)

theorem lowCoarseS35_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (142658960028195651 / 200000000000000000) (180142033540847367 / 250000000000000000) (kappa c) := bkappa (lowCoarseS35_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS35_hz20 hx hc).1 (lowCoarseS35_hz28 hx hc).2

theorem lowCoarseS35_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (69857966459152633 / 250000000000000000) (57341039971804349 / 200000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS35_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (69857966459152633 / 125000000000000000) (57341039971804349 / 100000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS35_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS35_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (69857950834152633 / 125000000000000000) (57341039971804349 / 100000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS35_hz31 hx hc) (lowCoarseS35_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (747571807034763091 / 1000000000000000000) (7572386676062201 / 10000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS35_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS35_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS35_hz35 hx hc) (lowCoarseS35_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (93022580255400057 / 125000000000000000) (7572386676062201 / 10000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS35_hz34 hx hc) (lowCoarseS35_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (93022580255400057 / 125000000000000000) (7572386676062201 / 10000000000000000) (ndm x c) := by
    convert (lowCoarseS35_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS35_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS35_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS35_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (11076096559836601 / 20000000000000000) (573410399718043491 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS35_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (1426589600281956509 / 1000000000000000000) (181622906498911903 / 125000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS35_hz40 hx hc) (lowCoarseS35_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS35_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS35_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (356647400070489127 / 500000000000000000) (145792316393898499 / 200000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS35_hz42 hx hc) (lowCoarseS35_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (356647400070489127 / 500000000000000000) (145792316393898499 / 200000000000000000) (nc1 x c) := by
    convert (lowCoarseS35_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS35_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (181307780379867391 / 250000000000000000) (729443737731699257 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS35_hz1 hx hc) (lowCoarseS35_hz13 hx hc).1 (lowCoarseS35_hz21 hx hc).2

theorem lowCoarseS35_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (94099739989647507 / 125000000000000000) (376398959958590029 / 500000000000000000) (kdot ((356647400070489127 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (204536933601190433 / 500000000000000000)) (a := (388304119370151441 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (81814773440476173 / 200000000000000000)) (a := (388304119370151439 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS35_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (759996723929311003 / 1000000000000000000) (379998361964655503 / 500000000000000000) (kdot ((145792316393898499 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (12372936298051473 / 31250000000000000)) (a := (47124533058822473 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (79186792307529427 / 200000000000000000)) (a := (188498132235289891 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS35_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (94099739989647507 / 125000000000000000) (379998361964655503 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS35_hz46 hx hc) (lowCoarseS35_hz48 hx hc).1 (lowCoarseS35_hz49 hx hc).2

theorem lowCoarseS35_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (169 / 400) (1089 / 2500) (c^2) := bsq (lowCoarseS35_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (1411 / 2500) (231 / 400) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS35_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (46954099927482371 / 62500000000000000) (379967103839266591 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS35_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (544841192805524551 / 1000000000000000000) (110865849775841327 / 200000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS35_hz53 hx hc) (lowCoarseS35_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (544841192805524551 / 1000000000000000000) (110865849775841327 / 200000000000000000) (npa c) := by
    convert (lowCoarseS35_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS35_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (239135267260467957 / 1000000000000000000) (241894571153323041 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS35_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (29462514311728451 / 62500000000000000) (48143286690292151 / 100000000000000000) (c * (kdot c)) := bmul (lowCoarseS35_hz1 hx hc) (lowCoarseS35_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-242297599642453553 / 1000000000000000000) (-9180226313373287 / 40000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS35_hz56 hx hc) (lowCoarseS35_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-242297599642453553 / 1000000000000000000) (-9180226313373287 / 40000000000000000) (npp c) := by
    convert (lowCoarseS35_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS35_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS35_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS35_hz3 hx hc) (lowCoarseS35_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS35_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS35_hz62 hx hc) (lowCoarseS35_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS35_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS35_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS35_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS35_hz65 hx hc) (lowCoarseS35_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS35_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS35_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS35_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS35_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (544841192805524551 / 1000000000000000000) (284362684224572397 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS35_hz55 hx hc) (lowCoarseS35_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (544841192805524551 / 1000000000000000000) (569691336007905267 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS35_hz69 hx hc) (lowCoarseS35_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (544841192805524551 / 1000000000000000000) (114277383700737317 / 200000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS35_hz70 hx hc) (lowCoarseS35_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (544841192805524551 / 1000000000000000000) (114277383700737317 / 200000000000000000) (nlam x c) := by
    convert (lowCoarseS35_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS35_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS35_hz73 hx hc) (lowCoarseS35_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS35_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS35_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS35_hz3 hx hc) (lowCoarseS35_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS35_hz76 hx hc) (lowCoarseS35_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS35_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS35_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS35_hz80 hx hc) (lowCoarseS35_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS35_hz81 hx hc) (lowCoarseS35_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS35_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS35_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-242297599642453553 / 1000000000000000000) (-43981648957541347 / 200000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS35_hz59 hx hc) (lowCoarseS35_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-184145381944200499 / 1000000000000000000) (-109954122393853367 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS35_hz84 hx hc) (lowCoarseS35_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (296851925377746777 / 1000000000000000000) (20405188164821161 / 62500000000000000) ((nlam x c)^2) := bsq (lowCoarseS35_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (508789471908158111 / 1000000000000000000) (265692493993732563 / 500000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS35_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (234307506006267437 / 500000000000000000) (491210528091841889 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS35_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (342277304247789293 / 500000000000000000) (140172825910280041 / 200000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS35_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (537647932257686687 / 250000000000000000) (440365920112656799 / 200000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS35_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (134820571629069073 / 1000000000000000000) (37952695324495839 / 250000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS35_hz86 hx hc) (lowCoarseS35_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-24662405157565713 / 500000000000000000) (41856658904129989 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS35_hz85 hx hc) (lowCoarseS35_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS35_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-24662405157565713 / 500000000000000000) (4185953390412999 / 100000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS35_hz92 hx hc) (lowCoarseS35_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-24662405157565713 / 500000000000000000) (11670072657204051 / 250000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS35_hz94 hx hc) (lowCoarseS35_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-24662405157565713 / 500000000000000000) (11670072657204051 / 250000000000000000) (nu x c) := by
    convert (lowCoarseS35_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS35_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-251895012689078993 / 1000000000000000000) (-9180226313373287 / 40000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS35_hz59 hx hc) (lowCoarseS35_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-251895012689078993 / 1000000000000000000) (-9180226313373287 / 40000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS35_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-191439384417832261 / 1000000000000000000) (-4319284545672733 / 25000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS35_hz50 hx hc) (lowCoarseS35_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-95721129708916131 / 500000000000000000) (-4319284545672733 / 25000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS35_hz99 hx hc) (lowCoarseS35_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-49065754035629619 / 250000000000000000) (-4319284545672733 / 25000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS35_hz100 hx hc) (lowCoarseS35_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B (-49065754035629619 / 250000000000000000) (-4319284545672733 / 25000000000000000) (nl x c) := by
    convert (lowCoarseS35_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS35_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (24662405157565713 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS35_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (49065754035629619 / 250000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS35_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (49065754035629619 / 250000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS35_hz103 hx hc) (lowCoarseS35_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS35_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) : B 0 (49065754035629619 / 250000000000000000) (ns x c) := by
    convert (lowCoarseS35_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS35 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (13 / 20) (33 / 50) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS35_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS35_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS35_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS35_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS35_hz38 hx hc).1) (lowCoarseS35_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS35_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS35_hz55 hx hc).1,(lowCoarseS35_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS35_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS35_hz68 hx hc).2 (lowCoarseS35_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS35_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS35_hz55 hx hc).1,(lowCoarseS35_hz64 hx hc).2]

theorem lowCoarseS36_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS36_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (33 / 50) (67 / 100) c := hc

theorem lowCoarseS36_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS36_hz2 hx hc) (lowCoarseS36_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS36_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS36_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS36_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS36_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS36_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS36_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS36_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS36_hz10 hx hc) (lowCoarseS36_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS36_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS36_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (364721868865849627 / 500000000000000000) (729443737731699257 / 1000000000000000000) (kdot ((33 / 50))) := by
    constructor
    · apply bkdot_lower (q := (452569637855251769 / 1000000000000000000)) (a := (84997756592480699 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56571204731906471 / 125000000000000000)) (a := (424988782962403493 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS36_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (1089 / 2500) (1089 / 2500) (((33 / 50) : ℝ)^2) := bsq (bpoint ((33 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (1411 / 2500) (1411 / 2500) ((1 : ℝ) - (((33 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS36_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (46954099927482371 / 62500000000000000) (751265598839717937 / 1000000000000000000) (√((1 : ℝ) - (((33 / 50) : ℝ)^2))) := bsqrt (lowCoarseS36_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (239135267260467957 / 1000000000000000000) (119567633630233979 / 500000000000000000) ((√((1 : ℝ) - (((33 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS36_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (481432866902921507 / 1000000000000000000) (48143286690292151 / 100000000000000000) (((33 / 50) : ℝ) * (kdot ((33 / 50)))) := bmul (bpoint ((33 / 50) : ℝ)) (lowCoarseS36_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (90071016770423683 / 125000000000000000) (180142033540847367 / 250000000000000000) (((√((1 : ℝ) - (((33 / 50) : ℝ)^2))) / Real.pi) + (((33 / 50) : ℝ) * (kdot ((33 / 50))))) := badd (lowCoarseS36_hz17 hx hc) (lowCoarseS36_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (90071016770423683 / 125000000000000000) (180142033540847367 / 250000000000000000) (kappa ((33 / 50))) := by rw [kappa_eq]; exact (lowCoarseS36_hz19 hx hc)

theorem lowCoarseS36_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (73370591556941763 / 100000000000000000) (22928309861544301 / 31250000000000000) (kdot ((67 / 100))) := by
    constructor
    · apply bkdot_lower (q := (222263801831945679 / 500000000000000000)) (a := (52286721208846107 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (444527603663891357 / 1000000000000000000)) (a := (209146884835384427 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS36_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (4489 / 10000) (4489 / 10000) (((67 / 100) : ℝ)^2) := bsq (bpoint ((67 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (5511 / 10000) (5511 / 10000) ((1 : ℝ) - (((67 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS36_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (371180549059349283 / 500000000000000000) (742361098118698567 / 1000000000000000000) (√((1 : ℝ) - (((67 / 100) : ℝ)^2))) := bsqrt (lowCoarseS36_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (236300876649436799 / 1000000000000000000) (236300876649436801 / 1000000000000000000) ((√((1 : ℝ) - (((67 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS36_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (122895740857877453 / 250000000000000000) (245791481715754907 / 500000000000000000) (((67 / 100) : ℝ) * (kdot ((67 / 100)))) := bmul (bpoint ((67 / 100) : ℝ)) (lowCoarseS36_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (727883840080946611 / 1000000000000000000) (145576768016189323 / 200000000000000000) (((√((1 : ℝ) - (((67 / 100) : ℝ)^2))) / Real.pi) + (((67 / 100) : ℝ) * (kdot ((67 / 100))))) := badd (lowCoarseS36_hz25 hx hc) (lowCoarseS36_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (727883840080946611 / 1000000000000000000) (145576768016189323 / 200000000000000000) (kappa ((67 / 100))) := by rw [kappa_eq]; exact (lowCoarseS36_hz27 hx hc)

theorem lowCoarseS36_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (90071016770423683 / 125000000000000000) (145576768016189323 / 200000000000000000) (kappa c) := bkappa (lowCoarseS36_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS36_hz20 hx hc).1 (lowCoarseS36_hz28 hx hc).2

theorem lowCoarseS36_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (54423231983810677 / 200000000000000000) (34928983229576317 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS36_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (54423231983810677 / 100000000000000000) (34928983229576317 / 62500000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS36_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS36_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (54423219483810677 / 100000000000000000) (34928983229576317 / 62500000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS36_hz31 hx hc) (lowCoarseS36_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (737720946454759931 / 1000000000000000000) (747571890638767311 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS36_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS36_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS36_hz35 hx hc) (lowCoarseS36_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (45895611341449831 / 62500000000000000) (747571890638767311 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS36_hz34 hx hc) (lowCoarseS36_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (45895611341449831 / 62500000000000000) (747571890638767311 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS36_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS36_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS36_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS36_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (539240227943787099 / 1000000000000000000) (558863731673221073 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS36_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (1441136268326778927 / 1000000000000000000) (58701914081573527 / 40000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS36_hz40 hx hc) (lowCoarseS36_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS36_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS36_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (720568134163389463 / 1000000000000000000) (92033580081910651 / 125000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS36_hz42 hx hc) (lowCoarseS36_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (720568134163389463 / 1000000000000000000) (92033580081910651 / 125000000000000000) (nc1 x c) := by
    convert (lowCoarseS36_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS36_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (364721868865849627 / 500000000000000000) (22928309861544301 / 31250000000000000) (kdot c) := bkdot (lowCoarseS36_hz1 hx hc) (lowCoarseS36_hz13 hx hc).1 (lowCoarseS36_hz21 hx hc).2

theorem lowCoarseS36_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (756118925474355641 / 1000000000000000000) (756118925474355643 / 1000000000000000000) (kdot ((720568134163389463 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (6296831235352011 / 15625000000000000)) (a := (383087496039674593 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (402997199062528703 / 1000000000000000000)) (a := (383087496039674591 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS36_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (763414019776639773 / 1000000000000000000) (30536560791065591 / 40000000000000000) (kdot ((92033580081910651 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (24358606702099523 / 62500000000000000)) (a := (371628388706024299 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (389737707233592367 / 1000000000000000000)) (a := (371628388706024297 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS36_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (756118925474355641 / 1000000000000000000) (30536560791065591 / 40000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS36_hz46 hx hc) (lowCoarseS36_hz48 hx hc).1 (lowCoarseS36_hz49 hx hc).2

theorem lowCoarseS36_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (1089 / 2500) (4489 / 10000) (c^2) := bsq (lowCoarseS36_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (5511 / 10000) (1411 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS36_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (371180549059349283 / 500000000000000000) (751265598839717937 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS36_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (541510654158312213 / 1000000000000000000) (275604007016251033 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS36_hz53 hx hc) (lowCoarseS36_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (541510654158312213 / 1000000000000000000) (275604007016251033 / 500000000000000000) (npa c) := by
    convert (lowCoarseS36_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS36_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (236300876649436799 / 1000000000000000000) (119567633630233979 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS36_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (481432866902921507 / 1000000000000000000) (245791481715754907 / 500000000000000000) (c * (kdot c)) := bmul (lowCoarseS36_hz1 hx hc) (lowCoarseS36_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-51056417356414603 / 200000000000000000) (-242297599642453549 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS36_hz56 hx hc) (lowCoarseS36_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-51056417356414603 / 200000000000000000) (-242297599642453549 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS36_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS36_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS36_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS36_hz3 hx hc) (lowCoarseS36_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS36_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS36_hz62 hx hc) (lowCoarseS36_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS36_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS36_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS36_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS36_hz65 hx hc) (lowCoarseS36_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS36_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS36_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS36_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS36_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (541510654158312213 / 1000000000000000000) (22624165344097609 / 40000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS36_hz55 hx hc) (lowCoarseS36_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (541510654158312213 / 1000000000000000000) (3541029998826893 / 6250000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS36_hz69 hx hc) (lowCoarseS36_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (541510654158312213 / 1000000000000000000) (284130191154042099 / 500000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS36_hz70 hx hc) (lowCoarseS36_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (541510654158312213 / 1000000000000000000) (284130191154042099 / 500000000000000000) (nlam x c) := by
    convert (lowCoarseS36_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS36_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS36_hz73 hx hc) (lowCoarseS36_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS36_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS36_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS36_hz3 hx hc) (lowCoarseS36_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS36_hz76 hx hc) (lowCoarseS36_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS36_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS36_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS36_hz80 hx hc) (lowCoarseS36_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS36_hz81 hx hc) (lowCoarseS36_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS36_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS36_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-51056417356414603 / 200000000000000000) (-232700186595828109 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS36_hz59 hx hc) (lowCoarseS36_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-609018512647723 / 3125000000000000) (-58175046648957027 / 500000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS36_hz84 hx hc) (lowCoarseS36_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (18327111785435201 / 62500000000000000) (322919862100930013 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS36_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (129804608992927109 / 250000000000000000) (542091511212381499 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS36_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (457908488787618501 / 1000000000000000000) (120195391007072891 / 250000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS36_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (135337871830115387 / 200000000000000000) (346692069432043529 / 500000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS36_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (531470579867459407 / 250000000000000000) (136145657298193809 / 62500000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS36_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (134614002011787559 / 1000000000000000000) (151899218100398551 / 1000000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS36_hz86 hx hc) (lowCoarseS36_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-60271922035483801 / 1000000000000000000) (35549124802484497 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS36_hz85 hx hc) (lowCoarseS36_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS36_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-60271922035483801 / 1000000000000000000) (17775999901242249 / 500000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS36_hz92 hx hc) (lowCoarseS36_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-60271922035483801 / 1000000000000000000) (5046594565896339 / 125000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS36_hz94 hx hc) (lowCoarseS36_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-60271922035483801 / 1000000000000000000) (5046594565896339 / 125000000000000000) (nu x c) := by
    convert (lowCoarseS36_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS36_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-52975899965739691 / 200000000000000000) (-242297599642453549 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS36_hz59 hx hc) (lowCoarseS36_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-52975899965739691 / 200000000000000000) (-242297599642453549 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS36_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-40442544744130491 / 200000000000000000) (-36641160137333519 / 200000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS36_hz50 hx hc) (lowCoarseS36_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-25276949840081557 / 125000000000000000) (-36641160137333519 / 200000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS36_hz99 hx hc) (lowCoarseS36_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-20703635544533867 / 100000000000000000) (-36641160137333519 / 200000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS36_hz100 hx hc) (lowCoarseS36_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B (-20703635544533867 / 100000000000000000) (-36641160137333519 / 200000000000000000) (nl x c) := by
    convert (lowCoarseS36_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS36_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (60271922035483801 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS36_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (20703635544533867 / 100000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS36_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (20703635544533867 / 100000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS36_hz103 hx hc) (lowCoarseS36_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS36_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) : B 0 (20703635544533867 / 100000000000000000) (ns x c) := by
    convert (lowCoarseS36_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS36 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (33 / 50) (67 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS36_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS36_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS36_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS36_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS36_hz38 hx hc).1) (lowCoarseS36_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS36_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS36_hz55 hx hc).1,(lowCoarseS36_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS36_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS36_hz68 hx hc).2 (lowCoarseS36_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS36_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS36_hz55 hx hc).1,(lowCoarseS36_hz64 hx hc).2]

theorem lowCoarseS37_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS37_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (67 / 100) (17 / 25) c := hc

theorem lowCoarseS37_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS37_hz2 hx hc) (lowCoarseS37_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS37_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS37_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS37_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS37_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS37_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS37_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS37_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS37_hz10 hx hc) (lowCoarseS37_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS37_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS37_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (73370591556941763 / 100000000000000000) (22928309861544301 / 31250000000000000) (kdot ((67 / 100))) := by
    constructor
    · apply bkdot_lower (q := (222263801831945679 / 500000000000000000)) (a := (52286721208846107 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (444527603663891357 / 1000000000000000000)) (a := (209146884835384427 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS37_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (4489 / 10000) (4489 / 10000) (((67 / 100) : ℝ)^2) := bsq (bpoint ((67 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (5511 / 10000) (5511 / 10000) ((1 : ℝ) - (((67 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS37_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (371180549059349283 / 500000000000000000) (742361098118698567 / 1000000000000000000) (√((1 : ℝ) - (((67 / 100) : ℝ)^2))) := bsqrt (lowCoarseS37_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (236300876649436799 / 1000000000000000000) (236300876649436801 / 1000000000000000000) ((√((1 : ℝ) - (((67 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS37_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (122895740857877453 / 250000000000000000) (245791481715754907 / 500000000000000000) (((67 / 100) : ℝ) * (kdot ((67 / 100)))) := bmul (bpoint ((67 / 100) : ℝ)) (lowCoarseS37_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (727883840080946611 / 1000000000000000000) (145576768016189323 / 200000000000000000) (((√((1 : ℝ) - (((67 / 100) : ℝ)^2))) / Real.pi) + (((67 / 100) : ℝ) * (kdot ((67 / 100))))) := badd (lowCoarseS37_hz17 hx hc) (lowCoarseS37_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (727883840080946611 / 1000000000000000000) (145576768016189323 / 200000000000000000) (kappa ((67 / 100))) := by rw [kappa_eq]; exact (lowCoarseS37_hz19 hx hc)

theorem lowCoarseS37_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (147604047826218153 / 200000000000000000) (738020239131090767 / 1000000000000000000) (kdot ((17 / 25))) := by
    constructor
    · apply bkdot_lower (q := (436435780471984763 / 1000000000000000000)) (a := (20575842303374401 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (218217890235992381 / 500000000000000000)) (a := (205758423033744009 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS37_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (289 / 625) (289 / 625) (((17 / 25) : ℝ)^2) := bsq (bpoint ((17 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (336 / 625) (336 / 625) ((1 : ℝ) - (((17 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS37_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (733212111192934401 / 1000000000000000000) (366606055596467201 / 500000000000000000) (√((1 : ℝ) - (((17 / 25) : ℝ)^2))) := bsqrt (lowCoarseS37_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (233388663662399819 / 1000000000000000000) (11669433183119991 / 50000000000000000) ((√((1 : ℝ) - (((17 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS37_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (12546344065228543 / 25000000000000000) (250926881304570861 / 500000000000000000) (((17 / 25) : ℝ) * (kdot ((17 / 25)))) := bmul (bpoint ((17 / 25) : ℝ)) (lowCoarseS37_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (735242426271541539 / 1000000000000000000) (367621213135770771 / 500000000000000000) (((√((1 : ℝ) - (((17 / 25) : ℝ)^2))) / Real.pi) + (((17 / 25) : ℝ) * (kdot ((17 / 25))))) := badd (lowCoarseS37_hz25 hx hc) (lowCoarseS37_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (735242426271541539 / 1000000000000000000) (367621213135770771 / 500000000000000000) (kappa ((17 / 25))) := by rw [kappa_eq]; exact (lowCoarseS37_hz27 hx hc)

theorem lowCoarseS37_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (727883840080946611 / 1000000000000000000) (367621213135770771 / 500000000000000000) (kappa c) := bkappa (lowCoarseS37_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS37_hz20 hx hc).1 (lowCoarseS37_hz28 hx hc).2

theorem lowCoarseS37_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (132378786864229229 / 500000000000000000) (272116159919053389 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS37_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (132378786864229229 / 250000000000000000) (272116159919053389 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS37_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS37_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (132378755614229229 / 250000000000000000) (272116159919053389 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS37_hz31 hx hc) (lowCoarseS37_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (181919457187947071 / 250000000000000000) (36886051558756827 / 50000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS37_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS37_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS37_hz35 hx hc) (lowCoarseS37_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (724286663760225649 / 1000000000000000000) (36886051558756827 / 50000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS37_hz34 hx hc) (lowCoarseS37_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (724286663760225649 / 1000000000000000000) (36886051558756827 / 50000000000000000) (ndm x c) := by
    convert (lowCoarseS37_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS37_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS37_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS37_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (262295585650459083 / 500000000000000000) (544232319838106779 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS37_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (1455767680161893221 / 1000000000000000000) (370549227170551777 / 250000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS37_hz40 hx hc) (lowCoarseS37_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS37_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS37_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (72788384008094661 / 100000000000000000) (371809035603992677 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS37_hz42 hx hc) (lowCoarseS37_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (72788384008094661 / 100000000000000000) (371809035603992677 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS37_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS37_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (73370591556941763 / 100000000000000000) (738020239131090767 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS37_hz1 hx hc) (lowCoarseS37_hz13 hx hc).1 (lowCoarseS37_hz21 hx hc).2

theorem lowCoarseS37_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (75949600572577603 / 100000000000000000) (23734250178930501 / 31250000000000000) (kdot ((72788384008094661 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (396844070236157649 / 1000000000000000000)) (a := (18889139539272593 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (24802754389759853 / 62500000000000000)) (a := (188891395392725929 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS37_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (766891881317780501 / 1000000000000000000) (766891881317780503 / 1000000000000000000) (kdot ((371809035603992677 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (95864548936929787 / 250000000000000000)) (a := (73233075314419841 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (383458195747719147 / 1000000000000000000)) (a := (366165376572099203 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS37_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (75949600572577603 / 100000000000000000) (766891881317780503 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS37_hz46 hx hc) (lowCoarseS37_hz48 hx hc).1 (lowCoarseS37_hz49 hx hc).2

theorem lowCoarseS37_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (4489 / 10000) (289 / 625) (c^2) := bsq (lowCoarseS37_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (336 / 625) (5511 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS37_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (733212111192934401 / 1000000000000000000) (742361098118698567 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS37_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (268981031674698789 / 500000000000000000) (547877515155181053 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS37_hz53 hx hc) (lowCoarseS37_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (268981031674698789 / 500000000000000000) (547877515155181053 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS37_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS37_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (233388663662399819 / 1000000000000000000) (236300876649436801 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS37_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (122895740857877453 / 250000000000000000) (250926881304570861 / 500000000000000000) (c * (kdot c)) := bmul (lowCoarseS37_hz1 hx hc) (lowCoarseS37_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-268465098946741903 / 1000000000000000000) (-255282086782073011 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS37_hz56 hx hc) (lowCoarseS37_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-268465098946741903 / 1000000000000000000) (-255282086782073011 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS37_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS37_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS37_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS37_hz3 hx hc) (lowCoarseS37_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS37_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS37_hz62 hx hc) (lowCoarseS37_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS37_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS37_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS37_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS37_hz65 hx hc) (lowCoarseS37_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS37_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS37_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS37_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS37_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (268981031674698789 / 500000000000000000) (140568408681279803 / 250000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS37_hz55 hx hc) (lowCoarseS37_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (268981031674698789 / 500000000000000000) (56322864415571993 / 100000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS37_hz69 hx hc) (lowCoarseS37_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (268981031674698789 / 500000000000000000) (8826941041429707 / 15625000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS37_hz70 hx hc) (lowCoarseS37_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (268981031674698789 / 500000000000000000) (8826941041429707 / 15625000000000000) (nlam x c) := by
    convert (lowCoarseS37_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS37_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS37_hz73 hx hc) (lowCoarseS37_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS37_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS37_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS37_hz3 hx hc) (lowCoarseS37_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS37_hz76 hx hc) (lowCoarseS37_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS37_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS37_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS37_hz80 hx hc) (lowCoarseS37_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS37_hz81 hx hc) (lowCoarseS37_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS37_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS37_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-268465098946741903 / 1000000000000000000) (-245684673735447571 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS37_hz59 hx hc) (lowCoarseS37_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-205883704799430991 / 1000000000000000000) (-24568467373544757 / 200000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS37_hz84 hx hc) (lowCoarseS37_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (72350795400785313 / 250000000000000000) (319139381857796753 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS37_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (264907442325492529 / 500000000000000000) (552967835827084377 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS37_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (447032164172915623 / 1000000000000000000) (235092557674507471 / 500000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS37_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (13372092793170643 / 20000000000000000) (85712556999125621 / 125000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS37_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (1050241712053647763 / 500000000000000000) (53854787877769893 / 25000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS37_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (33586055322042303 / 250000000000000000) (37984039554302939 / 250000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS37_hz86 hx hc) (lowCoarseS37_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-71539483511261779 / 1000000000000000000) (29093821349487971 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS37_hz85 hx hc) (lowCoarseS37_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS37_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-71539483511261779 / 1000000000000000000) (7274174087371993 / 250000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS37_hz92 hx hc) (lowCoarseS37_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-71539483511261779 / 1000000000000000000) (16958726537087093 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS37_hz94 hx hc) (lowCoarseS37_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-71539483511261779 / 1000000000000000000) (16958726537087093 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS37_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS37_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-278062511993367343 / 1000000000000000000) (-255282086782073011 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS37_hz59 hx hc) (lowCoarseS37_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-278062511993367343 / 1000000000000000000) (-255282086782073011 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS37_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-213243882946541387 / 1000000000000000000) (-378683057117823 / 1953125000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS37_hz50 hx hc) (lowCoarseS37_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-53311689486635347 / 250000000000000000) (-378683057117823 / 1953125000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS37_hz99 hx hc) (lowCoarseS37_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-109033757335613801 / 500000000000000000) (-378683057117823 / 1953125000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS37_hz100 hx hc) (lowCoarseS37_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B (-109033757335613801 / 500000000000000000) (-378683057117823 / 1953125000000000) (nl x c) := by
    convert (lowCoarseS37_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS37_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (71539483511261779 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS37_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (109033757335613801 / 500000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS37_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (109033757335613801 / 500000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS37_hz103 hx hc) (lowCoarseS37_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS37_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) : B 0 (109033757335613801 / 500000000000000000) (ns x c) := by
    convert (lowCoarseS37_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS37 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (67 / 100) (17 / 25) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS37_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS37_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS37_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS37_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS37_hz38 hx hc).1) (lowCoarseS37_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS37_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS37_hz55 hx hc).1,(lowCoarseS37_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS37_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS37_hz68 hx hc).2 (lowCoarseS37_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS37_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS37_hz55 hx hc).1,(lowCoarseS37_hz64 hx hc).2]

theorem lowCoarseS38_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS38_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (17 / 25) (69 / 100) c := hc

theorem lowCoarseS38_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS38_hz2 hx hc) (lowCoarseS38_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS38_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS38_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS38_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS38_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS38_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS38_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS38_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS38_hz10 hx hc) (lowCoarseS38_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS38_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS38_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (147604047826218153 / 200000000000000000) (738020239131090767 / 1000000000000000000) (kdot ((17 / 25))) := by
    constructor
    · apply bkdot_lower (q := (436435780471984763 / 1000000000000000000)) (a := (20575842303374401 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (218217890235992381 / 500000000000000000)) (a := (205758423033744009 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS38_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (289 / 625) (289 / 625) (((17 / 25) : ℝ)^2) := bsq (bpoint ((17 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (336 / 625) (336 / 625) ((1 : ℝ) - (((17 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS38_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (733212111192934401 / 1000000000000000000) (366606055596467201 / 500000000000000000) (√((1 : ℝ) - (((17 / 25) : ℝ)^2))) := bsqrt (lowCoarseS38_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (233388663662399819 / 1000000000000000000) (11669433183119991 / 50000000000000000) ((√((1 : ℝ) - (((17 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS38_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (12546344065228543 / 25000000000000000) (250926881304570861 / 500000000000000000) (((17 / 25) : ℝ) * (kdot ((17 / 25)))) := bmul (bpoint ((17 / 25) : ℝ)) (lowCoarseS38_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (735242426271541539 / 1000000000000000000) (367621213135770771 / 500000000000000000) (((√((1 : ℝ) - (((17 / 25) : ℝ)^2))) / Real.pi) + (((17 / 25) : ℝ) * (kdot ((17 / 25))))) := badd (lowCoarseS38_hz17 hx hc) (lowCoarseS38_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (735242426271541539 / 1000000000000000000) (367621213135770771 / 500000000000000000) (kappa ((17 / 25))) := by rw [kappa_eq]; exact (lowCoarseS38_hz19 hx hc)

theorem lowCoarseS38_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (742389493710301703 / 1000000000000000000) (148477898742060341 / 200000000000000000) (kdot ((69 / 100))) := by
    constructor
    · apply bkdot_lower (q := (107072391592885037 / 250000000000000000)) (a := (25290852313976981 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (428289566371540147 / 1000000000000000000)) (a := (202326818511815847 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS38_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (4761 / 10000) (4761 / 10000) (((69 / 100) : ℝ)^2) := bsq (bpoint ((69 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (5239 / 10000) (5239 / 10000) ((1 : ℝ) - (((69 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS38_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (723809367167902849 / 1000000000000000000) (14476187343358057 / 20000000000000000) (√((1 : ℝ) - (((69 / 100) : ℝ)^2))) := bsqrt (lowCoarseS38_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (57598919320494177 / 250000000000000000) (230395677281976709 / 1000000000000000000) ((√((1 : ℝ) - (((69 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS38_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (20489950026404327 / 40000000000000000) (512248750660108177 / 1000000000000000000) (((69 / 100) : ℝ) * (kdot ((69 / 100)))) := bmul (bpoint ((69 / 100) : ℝ)) (lowCoarseS38_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (742644427942084883 / 1000000000000000000) (371322213971042443 / 500000000000000000) (((√((1 : ℝ) - (((69 / 100) : ℝ)^2))) / Real.pi) + (((69 / 100) : ℝ) * (kdot ((69 / 100))))) := badd (lowCoarseS38_hz25 hx hc) (lowCoarseS38_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (742644427942084883 / 1000000000000000000) (371322213971042443 / 500000000000000000) (kappa ((69 / 100))) := by rw [kappa_eq]; exact (lowCoarseS38_hz27 hx hc)

theorem lowCoarseS38_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (735242426271541539 / 1000000000000000000) (371322213971042443 / 500000000000000000) (kappa c) := bkappa (lowCoarseS38_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS38_hz20 hx hc).1 (lowCoarseS38_hz28 hx hc).2

theorem lowCoarseS38_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (128677786028957557 / 500000000000000000) (264757573728458461 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS38_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (128677786028957557 / 250000000000000000) (264757573728458461 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS38_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS38_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (128677754778957557 / 250000000000000000) (264757573728458461 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS38_hz31 hx hc) (lowCoarseS38_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (179358408486302613 / 250000000000000000) (90959739330180179 / 125000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS38_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS38_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS38_hz35 hx hc) (lowCoarseS38_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (714042468953647817 / 1000000000000000000) (90959739330180179 / 125000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS38_hz34 hx hc) (lowCoarseS38_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (714042468953647817 / 1000000000000000000) (90959739330180179 / 125000000000000000) (ndm x c) := by
    convert (lowCoarseS38_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS38_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS38_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS38_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (254928323734710553 / 500000000000000000) (529515147456916923 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS38_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (1470484852543083077 / 1000000000000000000) (187116429064213021 / 125000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS38_hz40 hx hc) (lowCoarseS38_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS38_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS38_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (367621213135770769 / 500000000000000000) (751010380642423097 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS38_hz42 hx hc) (lowCoarseS38_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (367621213135770769 / 500000000000000000) (751010380642423097 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS38_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS38_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (147604047826218153 / 200000000000000000) (148477898742060341 / 200000000000000000) (kdot c) := bkdot (lowCoarseS38_hz1 hx hc) (lowCoarseS38_hz13 hx hc).1 (lowCoarseS38_hz21 hx hc).2

theorem lowCoarseS38_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (15258633864202331 / 20000000000000000) (95366461651264569 / 125000000000000000) (kdot ((367621213135770769 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (390610683577351393 / 1000000000000000000)) (a := (93096506376258643 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (12206583861792231 / 31250000000000000)) (a := (37238602550503457 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS38_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (770433200744085863 / 1000000000000000000) (154086640148817173 / 200000000000000000) (kdot ((751010380642423097 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (377091080753019821 / 1000000000000000000)) (a := (90150671256312833 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (18854554037650991 / 50000000000000000)) (a := (36060268502525133 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS38_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (15258633864202331 / 20000000000000000) (154086640148817173 / 200000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS38_hz46 hx hc) (lowCoarseS38_hz48 hx hc).1 (lowCoarseS38_hz49 hx hc).2

theorem lowCoarseS38_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (289 / 625) (4761 / 10000) (c^2) := bsq (lowCoarseS38_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (5239 / 10000) (336 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS38_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (723809367167902849 / 1000000000000000000) (366606055596467201 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS38_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (534185962242579137 / 1000000000000000000) (544328968010784009 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS38_hz53 hx hc) (lowCoarseS38_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (534185962242579137 / 1000000000000000000) (544328968010784009 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS38_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS38_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (57598919320494177 / 250000000000000000) (11669433183119991 / 50000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS38_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (12546344065228543 / 25000000000000000) (512248750660108177 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS38_hz1 hx hc) (lowCoarseS38_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-281853073378131469 / 1000000000000000000) (-2684650989467419 / 10000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS38_hz56 hx hc) (lowCoarseS38_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-281853073378131469 / 1000000000000000000) (-2684650989467419 / 10000000000000000) (npp c) := by
    convert (lowCoarseS38_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS38_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS38_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS38_hz3 hx hc) (lowCoarseS38_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS38_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS38_hz62 hx hc) (lowCoarseS38_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS38_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS38_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS38_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS38_hz65 hx hc) (lowCoarseS38_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS38_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS38_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS38_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS38_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (534185962242579137 / 1000000000000000000) (69840635947590271 / 125000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS38_hz55 hx hc) (lowCoarseS38_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (534185962242579137 / 1000000000000000000) (279837034940931979 / 500000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS38_hz69 hx hc) (lowCoarseS38_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (534185962242579137 / 1000000000000000000) (140342413094411319 / 250000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS38_hz70 hx hc) (lowCoarseS38_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (534185962242579137 / 1000000000000000000) (140342413094411319 / 250000000000000000) (nlam x c) := by
    convert (lowCoarseS38_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS38_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS38_hz73 hx hc) (lowCoarseS38_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS38_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS38_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS38_hz3 hx hc) (lowCoarseS38_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS38_hz76 hx hc) (lowCoarseS38_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS38_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS38_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS38_hz80 hx hc) (lowCoarseS38_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS38_hz81 hx hc) (lowCoarseS38_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS38_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS38_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-281853073378131469 / 1000000000000000000) (-12943384295005823 / 50000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS38_hz59 hx hc) (lowCoarseS38_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-108574482731135763 / 500000000000000000) (-12943384295005823 / 100000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS38_hz84 hx hc) (lowCoarseS38_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (285354642257030183 / 1000000000000000000) (315135886610598299 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS38_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (270290712694831597 / 500000000000000000) (564016591832677229 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS38_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (435983408167322771 / 1000000000000000000) (229709287305168403 / 500000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS38_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (330145198423103971 / 500000000000000000) (135560846059669723 / 200000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS38_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (518590864991984013 / 250000000000000000) (2129384790477376359 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS38_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (13400802125249421 / 100000000000000000) (6076772806545087 / 40000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS38_hz86 hx hc) (lowCoarseS38_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-20785236052444329 / 250000000000000000) (4497095442713789 / 200000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS38_hz85 hx hc) (lowCoarseS38_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS38_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-20785236052444329 / 250000000000000000) (11244176106784473 / 500000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS38_hz92 hx hc) (lowCoarseS38_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-20785236052444329 / 250000000000000000) (682727723456379 / 25000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS38_hz94 hx hc) (lowCoarseS38_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-20785236052444329 / 250000000000000000) (682727723456379 / 25000000000000000) (nu x c) := by
    convert (lowCoarseS38_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS38_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-291450486424756909 / 1000000000000000000) (-2684650989467419 / 10000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS38_hz59 hx hc) (lowCoarseS38_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-291450486424756909 / 1000000000000000000) (-2684650989467419 / 10000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS38_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-56135782778661553 / 250000000000000000) (-102410266253629637 / 500000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS38_hz50 hx hc) (lowCoarseS38_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-224546006114646213 / 1000000000000000000) (-102410266253629637 / 500000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS38_hz99 hx hc) (lowCoarseS38_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-229366762839332427 / 1000000000000000000) (-102410266253629637 / 500000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS38_hz100 hx hc) (lowCoarseS38_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B (-229366762839332427 / 1000000000000000000) (-102410266253629637 / 500000000000000000) (nl x c) := by
    convert (lowCoarseS38_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS38_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (20785236052444329 / 250000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS38_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (229366762839332427 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS38_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (229366762839332427 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS38_hz103 hx hc) (lowCoarseS38_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS38_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) : B 0 (229366762839332427 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS38_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS38 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (17 / 25) (69 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS38_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS38_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS38_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS38_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS38_hz38 hx hc).1) (lowCoarseS38_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS38_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS38_hz55 hx hc).1,(lowCoarseS38_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS38_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS38_hz68 hx hc).2 (lowCoarseS38_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS38_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS38_hz55 hx hc).1,(lowCoarseS38_hz64 hx hc).2]

theorem lowCoarseS39_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS39_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (69 / 100) (7 / 10) c := hc

theorem lowCoarseS39_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS39_hz2 hx hc) (lowCoarseS39_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS39_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS39_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS39_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS39_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS39_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS39_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS39_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS39_hz10 hx hc) (lowCoarseS39_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS39_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS39_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (742389493710301703 / 1000000000000000000) (148477898742060341 / 200000000000000000) (kdot ((69 / 100))) := by
    constructor
    · apply bkdot_lower (q := (107072391592885037 / 250000000000000000)) (a := (25290852313976981 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (428289566371540147 / 1000000000000000000)) (a := (202326818511815847 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS39_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (4761 / 10000) (4761 / 10000) (((69 / 100) : ℝ)^2) := bsq (bpoint ((69 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (5239 / 10000) (5239 / 10000) ((1 : ℝ) - (((69 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS39_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (723809367167902849 / 1000000000000000000) (14476187343358057 / 20000000000000000) (√((1 : ℝ) - (((69 / 100) : ℝ)^2))) := bsqrt (lowCoarseS39_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (57598919320494177 / 250000000000000000) (230395677281976709 / 1000000000000000000) ((√((1 : ℝ) - (((69 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS39_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (20489950026404327 / 40000000000000000) (512248750660108177 / 1000000000000000000) (((69 / 100) : ℝ) * (kdot ((69 / 100)))) := bmul (bpoint ((69 / 100) : ℝ)) (lowCoarseS39_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (742644427942084883 / 1000000000000000000) (371322213971042443 / 500000000000000000) (((√((1 : ℝ) - (((69 / 100) : ℝ)^2))) / Real.pi) + (((69 / 100) : ℝ) * (kdot ((69 / 100))))) := badd (lowCoarseS39_hz17 hx hc) (lowCoarseS39_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (742644427942084883 / 1000000000000000000) (371322213971042443 / 500000000000000000) (kappa ((69 / 100))) := by rw [kappa_eq]; exact (lowCoarseS39_hz19 hx hc)

theorem lowCoarseS39_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (746816688893365019 / 1000000000000000000) (373408344446682511 / 500000000000000000) (kdot ((7 / 10))) := by
    constructor
    · apply bkdot_lower (q := (210042012604201471 / 500000000000000000)) (a := (397699415092071779 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (420084025208402941 / 1000000000000000000)) (a := (397699415092071777 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS39_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (49 / 100) (49 / 100) (((7 / 10) : ℝ)^2) := bsq (bpoint ((7 / 10) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (51 / 100) (51 / 100) ((1 : ℝ) - (((7 / 10) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS39_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (714142842854284999 / 1000000000000000000) (142828568570857 / 200000000000000) (√((1 : ℝ) - (((7 / 10) : ℝ)^2))) := bsqrt (lowCoarseS39_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (45463745405583233 / 200000000000000000) (113659363513958083 / 500000000000000000) ((√((1 : ℝ) - (((7 / 10) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS39_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (522771682225355513 / 1000000000000000000) (130692920556338879 / 250000000000000000) (((7 / 10) : ℝ) * (kdot ((7 / 10)))) := bmul (bpoint ((7 / 10) : ℝ)) (lowCoarseS39_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (375045204626635839 / 500000000000000000) (375045204626635841 / 500000000000000000) (((√((1 : ℝ) - (((7 / 10) : ℝ)^2))) / Real.pi) + (((7 / 10) : ℝ) * (kdot ((7 / 10))))) := badd (lowCoarseS39_hz25 hx hc) (lowCoarseS39_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (375045204626635839 / 500000000000000000) (375045204626635841 / 500000000000000000) (kappa ((7 / 10))) := by rw [kappa_eq]; exact (lowCoarseS39_hz27 hx hc)

theorem lowCoarseS39_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (742644427942084883 / 1000000000000000000) (375045204626635841 / 500000000000000000) (kappa c) := bkappa (lowCoarseS39_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS39_hz20 hx hc).1 (lowCoarseS39_hz28 hx hc).2

theorem lowCoarseS39_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (124954795373364159 / 500000000000000000) (257355572057915117 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS39_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (124954795373364159 / 250000000000000000) (257355572057915117 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS39_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS39_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (124954764123364159 / 250000000000000000) (257355572057915117 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS39_hz31 hx hc) (lowCoarseS39_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (17674470580710767 / 25000000000000000) (143486744212255403 / 200000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS39_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS39_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS39_hz35 hx hc) (lowCoarseS39_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (140717531647373609 / 200000000000000000) (143486744212255403 / 200000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS39_hz34 hx hc) (lowCoarseS39_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (140717531647373609 / 200000000000000000) (143486744212255403 / 200000000000000000) (ndm x c) := by
    convert (lowCoarseS39_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS39_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS39_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS39_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (49503559282323983 / 100000000000000000) (102942228823166047 / 200000000000000000) ((ndm x c)^2) := bsq (lowCoarseS39_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (297057771176833953 / 200000000000000000) (377938121789971361 / 250000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS39_hz40 hx hc) (lowCoarseS39_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS39_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS39_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (371322213971042441 / 500000000000000000) (189611525644926547 / 250000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS39_hz42 hx hc) (lowCoarseS39_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (371322213971042441 / 500000000000000000) (189611525644926547 / 250000000000000000) (nc1 x c) := by
    convert (lowCoarseS39_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS39_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (742389493710301703 / 1000000000000000000) (373408344446682511 / 500000000000000000) (kdot c) := bkdot (lowCoarseS39_hz1 hx hc) (lowCoarseS39_hz13 hx hc).1 (lowCoarseS39_hz21 hx hc).2

theorem lowCoarseS39_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (383214361487687599 / 500000000000000000) (958035903719219 / 1250000000000000) (kdot ((371322213971042441 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (384292931958598323 / 1000000000000000000)) (a := (91723225998768467 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (192146465979299161 / 500000000000000000)) (a := (183446451997536933 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS39_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (193510278564794717 / 250000000000000000) (77404111425917887 / 100000000000000000) (kdot ((189611525644926547 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (1853158210695587 / 5000000000000000)) (a := (44366923466043697 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (370631642139117399 / 1000000000000000000)) (a := (177467693864174787 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS39_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (383214361487687599 / 500000000000000000) (77404111425917887 / 100000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS39_hz46 hx hc) (lowCoarseS39_hz48 hx hc).1 (lowCoarseS39_hz49 hx hc).2

theorem lowCoarseS39_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (4761 / 10000) (49 / 100) (c^2) := bsq (lowCoarseS39_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (51 / 100) (5239 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS39_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (714142842854284999 / 1000000000000000000) (14476187343358057 / 20000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS39_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (53017214354342819 / 100000000000000000) (270276457489167559 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS39_hz53 hx hc) (lowCoarseS39_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (53017214354342819 / 100000000000000000) (270276457489167559 / 500000000000000000) (npa c) := by
    convert (lowCoarseS39_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS39_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (45463745405583233 / 200000000000000000) (230395677281976709 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS39_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (20489950026404327 / 40000000000000000) (130692920556338879 / 250000000000000000) (c * (kdot c)) := bmul (lowCoarseS39_hz1 hx hc) (lowCoarseS39_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-295452955197439351 / 1000000000000000000) (-140926536689065733 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS39_hz56 hx hc) (lowCoarseS39_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-295452955197439351 / 1000000000000000000) (-140926536689065733 / 500000000000000000) (npp c) := by
    convert (lowCoarseS39_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS39_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS39_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS39_hz3 hx hc) (lowCoarseS39_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS39_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS39_hz62 hx hc) (lowCoarseS39_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS39_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS39_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS39_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS39_hz65 hx hc) (lowCoarseS39_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS39_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS39_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS39_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS39_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (53017214354342819 / 100000000000000000) (554949034548273277 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS39_hz55 hx hc) (lowCoarseS39_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (53017214354342819 / 100000000000000000) (69486450413274681 / 125000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS39_hz69 hx hc) (lowCoarseS39_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (53017214354342819 / 100000000000000000) (278793592900989383 / 500000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS39_hz70 hx hc) (lowCoarseS39_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (53017214354342819 / 100000000000000000) (278793592900989383 / 500000000000000000) (nlam x c) := by
    convert (lowCoarseS39_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS39_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS39_hz73 hx hc) (lowCoarseS39_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS39_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS39_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS39_hz3 hx hc) (lowCoarseS39_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS39_hz76 hx hc) (lowCoarseS39_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS39_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS39_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS39_hz80 hx hc) (lowCoarseS39_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS39_hz81 hx hc) (lowCoarseS39_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS39_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS39_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-295452955197439351 / 1000000000000000000) (-136127830165753013 / 500000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS39_hz59 hx hc) (lowCoarseS39_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-228692734652193209 / 1000000000000000000) (-136127830165753013 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS39_hz84 hx hc) (lowCoarseS39_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (11243300071577337 / 40000000000000000) (310903469770570391 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS39_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (68940093294178313 / 125000000000000000) (287620245259173101 / 500000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS39_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (212379754740826899 / 500000000000000000) (56059906705821687 / 125000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS39_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (162933941653061847 / 250000000000000000) (167421484143794531 / 250000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS39_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (1023744148235374221 / 500000000000000000) (1051940209278489907 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS39_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (133601938261407327 / 1000000000000000000) (37961568609021367 / 250000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS39_hz86 hx hc) (lowCoarseS39_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-47545398195392941 / 500000000000000000) (3143688854066491 / 200000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS39_hz85 hx hc) (lowCoarseS39_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS39_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-47545398195392941 / 500000000000000000) (1965164908791557 / 125000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS39_hz92 hx hc) (lowCoarseS39_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-47545398195392941 / 500000000000000000) (2054207599501867 / 100000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS39_hz94 hx hc) (lowCoarseS39_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-47545398195392941 / 500000000000000000) (2054207599501867 / 100000000000000000) (nu x c) := by
    convert (lowCoarseS39_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS39_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-305050368244064791 / 1000000000000000000) (-140926536689065733 / 500000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS39_hz59 hx hc) (lowCoarseS39_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-305050368244064791 / 1000000000000000000) (-140926536689065733 / 500000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS39_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-47224305388161749 / 200000000000000000) (-216020291095886019 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS39_hz50 hx hc) (lowCoarseS39_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-118062200970404373 / 500000000000000000) (-216020291095886019 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS39_hz99 hx hc) (lowCoarseS39_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-3011814483318687 / 12500000000000000) (-216020291095886019 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS39_hz100 hx hc) (lowCoarseS39_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B (-3011814483318687 / 12500000000000000) (-216020291095886019 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS39_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS39_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (47545398195392941 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS39_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (3011814483318687 / 12500000000000000) |(nl x c)| := bweaken (babs (lowCoarseS39_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (3011814483318687 / 12500000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS39_hz103 hx hc) (lowCoarseS39_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS39_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) : B 0 (3011814483318687 / 12500000000000000) (ns x c) := by
    convert (lowCoarseS39_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS39 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (69 / 100) (7 / 10) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS39_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS39_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS39_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS39_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS39_hz38 hx hc).1) (lowCoarseS39_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS39_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS39_hz55 hx hc).1,(lowCoarseS39_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS39_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS39_hz68 hx hc).2 (lowCoarseS39_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS39_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS39_hz55 hx hc).1,(lowCoarseS39_hz64 hx hc).2]

end BstLean.BlueprintLow
