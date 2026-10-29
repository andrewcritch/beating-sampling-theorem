import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255 BstLean.Part264b
theorem lowGroupedE60W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE60W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (69337607 / 200000000) (707659223 / 1000000000) c := hc

theorem lowGroupedE60W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE60W_hz2 hx hc) (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE60W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE60W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE60W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE60W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE60W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE60W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE60W_hz11 hx hc) (lowGroupedE60W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE60W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE60W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (4901549946171543 / 8000000000000000) (612693743793992451 / 1000000000000000000) (kdot ((69337607 / 200000000))) := by
    constructor
    · apply bkdot_lower (q := (348254558305080577 / 500000000000000000)) (a := (76047405676737343 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (696509116610161153 / 1000000000000000000)) (a := (38023702787067487 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE60W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (4807703744486449 / 40000000000000000) (4807703744486449 / 40000000000000000) (((69337607 / 200000000) : ℝ)^2) := bsq (bpoint ((69337607 / 200000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (35192296255513551 / 40000000000000000) (35192296255513551 / 40000000000000000) ((1 : ℝ) - (((69337607 / 200000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE60W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (117247561700915473 / 125000000000000000) (187596098721464757 / 200000000000000000) (√((1 : ℝ) - (((69337607 / 200000000) : ℝ)^2))) := bsqrt (lowGroupedE60W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (298568464162763027 / 1000000000000000000) (74642116040690757 / 250000000000000000) ((√((1 : ℝ) - (((69337607 / 200000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE60W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (212413589911571001 / 1000000000000000000) (13275849380795793 / 62500000000000000) (((69337607 / 200000000) : ℝ) * (kdot ((69337607 / 200000000)))) := bmul (bpoint ((69337607 / 200000000) : ℝ)) (lowGroupedE60W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (127745513518583507 / 250000000000000000) (127745513563873929 / 250000000000000000) (((√((1 : ℝ) - (((69337607 / 200000000) : ℝ)^2))) / Real.pi) + (((69337607 / 200000000) : ℝ) * (kdot ((69337607 / 200000000))))) := badd (lowGroupedE60W_hz18 hx hc) (lowGroupedE60W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (127745513518583507 / 250000000000000000) (127745513563873929 / 250000000000000000) (kappa ((69337607 / 200000000))) := by rw [kappa_eq]; exact (lowGroupedE60W_hz20 hx hc)

theorem lowGroupedE60W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (750248783436121301 / 1000000000000000000) (750248783436121303 / 1000000000000000000) (kdot ((707659223 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (413755799700847397 / 1000000000000000000)) (a := (196154146795548701 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (103438949925211849 / 250000000000000000)) (a := (1961541467955487 / 5000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE60W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (500781575896963729 / 1000000000000000000) (500781575896963729 / 1000000000000000000) (((707659223 / 1000000000) : ℝ)^2) := bsq (bpoint ((707659223 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (499218424103036271 / 1000000000000000000) (499218424103036271 / 1000000000000000000) ((1 : ℝ) - (((707659223 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE60W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (706553907428892697 / 1000000000000000000) (353276953714446349 / 500000000000000000) (√((1 : ℝ) - (((707659223 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE60W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (56225773464100851 / 250000000000000000) (44980618771280681 / 200000000000000000) ((√((1 : ℝ) - (((707659223 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE60W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (530920471143100869 / 1000000000000000000) (66365058892887609 / 125000000000000000) (((707659223 / 1000000000) : ℝ) * (kdot ((707659223 / 1000000000)))) := bmul (bpoint ((707659223 / 1000000000) : ℝ)) (lowGroupedE60W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (755823564999504273 / 1000000000000000000) (755823564999504277 / 1000000000000000000) (((√((1 : ℝ) - (((707659223 / 1000000000) : ℝ)^2))) / Real.pi) + (((707659223 / 1000000000) : ℝ) * (kdot ((707659223 / 1000000000))))) := badd (lowGroupedE60W_hz26 hx hc) (lowGroupedE60W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (755823564999504273 / 1000000000000000000) (755823564999504277 / 1000000000000000000) (kappa ((707659223 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE60W_hz28 hx hc)

theorem lowGroupedE60W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (127745513518583507 / 250000000000000000) (755823564999504277 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE60W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE60W_hz21 hx hc).1 (lowGroupedE60W_hz29 hx hc).2

theorem lowGroupedE60W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (244176435000495723 / 1000000000000000000) (122254486481416493 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE60W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (244176435000495723 / 500000000000000000) (122254486481416493 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE60W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (244176372500495723 / 500000000000000000) (122254486481416493 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE60W_hz32 hx hc) (lowGroupedE60W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (698822398754498599 / 1000000000000000000) (988956971688521919 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE60W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE60W_hz36 hx hc) (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (173857808440733991 / 250000000000000000) (988956971688521919 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE60W_hz35 hx hc) (lowGroupedE60W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (173857808440733991 / 250000000000000000) (988956971688521919 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE60W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE60W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE60W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE60W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (96724920178607857 / 200000000000000000) (195607178370266389 / 200000000000000000) ((ndm x c)^2) := bsq (lowGroupedE60W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (204392821629733611 / 200000000000000000) (1523163479090085989 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE60W_hz41 hx hc) (lowGroupedE60W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE60W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE60W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (510982054074334027 / 1000000000000000000) (764170996323581177 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE60W_hz43 hx hc) (lowGroupedE60W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (510982054074334027 / 1000000000000000000) (764170996323581177 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE60W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE60W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (670718144633497169 / 1000000000000000000) (670718144633522953 / 1000000000000000000) (kdot ((510982054074334027 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (284447911737666121 / 500000000000000000)) (a := (517234728889911063 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (568895823475332241 / 1000000000000000000)) (a := (517234728889870563 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE60W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (388425823503263547 / 500000000000000000) (97106455875815887 / 125000000000000000) (kdot ((764170996323581177 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (365618589762112359 / 1000000000000000000)) (a := (175260306606239107 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (182809294881056179 / 500000000000000000)) (a := (87630153303119553 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE60W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (670718144633497169 / 1000000000000000000) (97106455875815887 / 125000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE60W_hz47 hx hc) (lowGroupedE60W_hz48 hx hc).1 (lowGroupedE60W_hz49 hx hc).2

theorem lowGroupedE60W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE60W_hz51 hx hc) (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE60W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (41919884039593573 / 125000000000000000) (97106455875815887 / 250000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE60W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (41919884039593573 / 125000000000000000) (194512651221838819 / 500000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE60W_hz54 hx hc) (lowGroupedE60W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (7502487834361213 / 20000000000000000) (93781097929515163 / 250000000000000000) ((kdot ((707659223 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE60W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (7502487834361213 / 20000000000000000) (187861935329237371 / 500000000000000000) (((kdot ((707659223 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE60W_hz56 hx hc) (lowGroupedE60W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE60W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE60W_hz58 hx hc) (lowGroupedE60W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE60W_hz3 hx hc) (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE60W_hz60 hx hc) (lowGroupedE60W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE60W_hz4 hx hc) (lowGroupedE60W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE60W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE60W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (612473992687085979 / 1000000000000000000) (30648159433254501 / 50000000000000000) (√(((kdot ((707659223 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE60W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (612473992687085979 / 1000000000000000000) (624143528552588969 / 1000000000000000000) ((√(((kdot ((707659223 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE60W_hz65 hx hc) (lowGroupedE60W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (612473992687085979 / 1000000000000000000) (625342486433417149 / 1000000000000000000) (((√(((kdot ((707659223 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE60W_hz66 hx hc) (lowGroupedE60W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (866169027058876827 / 1000000000000000000) (55272989090140733 / 62500000000000000) ((√(2 : ℝ)) * (((√(((kdot ((707659223 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE60W_hz4 hx hc) (lowGroupedE60W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (866169027058876827 / 1000000000000000000) (55272989090140733 / 62500000000000000) (neb x (kdot (707659223 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE60W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE60W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE60W_hz4 hx hc) (lowGroupedE60W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE60W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE60W_hz3 hx hc) (lowGroupedE60W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE60W_hz71 hx hc) (lowGroupedE60W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE60W_hz4 hx hc) (lowGroupedE60W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE60W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE60W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE60W_hz4 hx hc) (lowGroupedE60W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE60W_hz76 hx hc) (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE60W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE60W_hz4 hx hc) (lowGroupedE60W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE60W_hz79 hx hc) (lowGroupedE60W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE60W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE60W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE60W_hz70 hx hc) (lowGroupedE60W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE60W_hz82 hx hc) (lowGroupedE60W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE60W_hz4 hx hc) (lowGroupedE60W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE60W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE60W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (72387744162594241 / 125000000000000000) (623718929040699901 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE60W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (72387744162594241 / 62500000000000000) (623718929040699901 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE60W_hz70 hx hc) (lowGroupedE60W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (530483745152141 / 25000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE60W_hz87 hx hc) (lowGroupedE60W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE60W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (10754350841652949 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE60W_hz89 hx hc) (lowGroupedE60W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (10754350841652949 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (10754350841652949 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE60W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE60W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE60W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE60W_hz94 hx hc) (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE60W_hz96 hx hc) (lowGroupedE60W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE60W_hz97 hx hc) (lowGroupedE60W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE60W_hz98 hx hc) (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE60W_hz95 hx hc) (lowGroupedE60W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE60W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (11147318879382239 / 250000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE60W_hz93 hx hc) (lowGroupedE60W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (580827627244667 / 12500000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE60W_hz100 hx hc) (lowGroupedE60W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (41919884039593573 / 62500000000000000) (194512651221838819 / 250000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (46890548964757581 / 62500000000000000) (782106450677457023 / 1000000000000000000) ((neb x (kdot (707659223 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE60W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE60W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE60W_hz106 hx hc) (lowGroupedE60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (46890548964757581 / 62500000000000000) (782421760689329153 / 1000000000000000000) (((neb x (kdot (707659223 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE60W_hz105 hx hc) (lowGroupedE60W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (503205472039813697 / 1000000000000000000) (304381862090681041 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (707659223 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE60W_hz104 hx hc) (lowGroupedE60W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (503205472039813697 / 1000000000000000000) (327614967180467721 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (707659223 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE60W_hz103 hx hc) (lowGroupedE60W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) : B (503205472039813697 / 1000000000000000000) (327614967180467721 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (707659223 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE60W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE60W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (69337607 / 200000000) (707659223 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (707659223 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (131045987 / 200000000) :=
  (lowGroupedE60W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE60C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE60C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (26390681 / 62500000) (598881659 / 1000000000) c := hc

theorem lowGroupedE60C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE60C_hz2 hx hc) (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE60C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE60C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE60C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE60C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE60C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE60C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE60C_hz11 hx hc) (lowGroupedE60C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE60C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE60C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (319379938156620903 / 500000000000000000) (127751975263998689 / 200000000000000000) (kdot ((26390681 / 62500000))) := by
    constructor
    · apply bkdot_lower (q := (31867759915539359 / 50000000000000000)) (a := (567434659378093899 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (637355198310787179 / 1000000000000000000)) (a := (11348693187349769 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE60C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (696468043643761 / 3906250000000000) (696468043643761 / 3906250000000000) (((26390681 / 62500000) : ℝ)^2) := bsq (bpoint ((26390681 / 62500000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (3209781956356239 / 3906250000000000) (3209781956356239 / 3906250000000000) ((1 : ℝ) - (((26390681 / 62500000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE60C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (28327468808367961 / 31250000000000000) (906479001867774753 / 1000000000000000000) (√((1 : ℝ) - (((26390681 / 62500000) : ℝ)^2))) := bsqrt (lowGroupedE60C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (4508456686133243 / 15625000000000000) (144270613956263777 / 500000000000000000) ((√((1 : ℝ) - (((26390681 / 62500000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE60C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (269716930102115529 / 1000000000000000000) (53943386020993283 / 200000000000000000) (((26390681 / 62500000) : ℝ) * (kdot ((26390681 / 62500000)))) := bmul (bpoint ((26390681 / 62500000) : ℝ)) (lowGroupedE60C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (558258158014643081 / 1000000000000000000) (558258158017493969 / 1000000000000000000) (((√((1 : ℝ) - (((26390681 / 62500000) : ℝ)^2))) / Real.pi) + (((26390681 / 62500000) : ℝ) * (kdot ((26390681 / 62500000))))) := badd (lowGroupedE60C_hz18 hx hc) (lowGroupedE60C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (558258158014643081 / 1000000000000000000) (558258158017493969 / 1000000000000000000) (kappa ((26390681 / 62500000))) := by rw [kappa_eq]; exact (lowGroupedE60C_hz20 hx hc)

theorem lowGroupedE60C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (704388023829950067 / 1000000000000000000) (704388023829950119 / 1000000000000000000) (kdot ((598881659 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (500873551927239177 / 1000000000000000000)) (a := (232173103162247473 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (62609193990904897 / 125000000000000000)) (a := (92869241264898973 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE60C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (358659241486592281 / 1000000000000000000) (358659241486592281 / 1000000000000000000) (((598881659 / 1000000000) : ℝ)^2) := bsq (bpoint ((598881659 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (641340758513407719 / 1000000000000000000) (641340758513407719 / 1000000000000000000) ((1 : ℝ) - (((598881659 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE60C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (800837535654646821 / 1000000000000000000) (400418767827323411 / 500000000000000000) (√((1 : ℝ) - (((598881659 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE60C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (254914504825938033 / 1000000000000000000) (127457252412969017 / 500000000000000000) ((√((1 : ℝ) - (((598881659 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE60C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (42184506829101203 / 100000000000000000) (210922534145506031 / 500000000000000000) (((598881659 / 1000000000) : ℝ) * (kdot ((598881659 / 1000000000)))) := bmul (bpoint ((598881659 / 1000000000) : ℝ)) (lowGroupedE60C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (676759573116950063 / 1000000000000000000) (42297473319809381 / 62500000000000000) (((√((1 : ℝ) - (((598881659 / 1000000000) : ℝ)^2))) / Real.pi) + (((598881659 / 1000000000) : ℝ) * (kdot ((598881659 / 1000000000))))) := badd (lowGroupedE60C_hz26 hx hc) (lowGroupedE60C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (676759573116950063 / 1000000000000000000) (42297473319809381 / 62500000000000000) (kappa ((598881659 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE60C_hz28 hx hc)

theorem lowGroupedE60C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (558258158014643081 / 1000000000000000000) (42297473319809381 / 62500000000000000) (kappa c) := bkappa (lowGroupedE60C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE60C_hz21 hx hc).1 (lowGroupedE60C_hz29 hx hc).2

theorem lowGroupedE60C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (20202526680190619 / 62500000000000000) (441741841985356919 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE60C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (20202526680190619 / 31250000000000000) (441741841985356919 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE60C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (20202522773940619 / 31250000000000000) (441741841985356919 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE60C_hz32 hx hc) (lowGroupedE60C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (402020126600055873 / 500000000000000000) (234984531933847967 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE60C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE60C_hz36 hx hc) (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (800649088208549111 / 1000000000000000000) (234984531933847967 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE60C_hz35 hx hc) (lowGroupedE60C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (800649088208549111 / 1000000000000000000) (234984531933847967 / 250000000000000000) (ndm x c) := by
    convert (lowGroupedE60C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE60C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE60C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE60C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (128207792489836211 / 200000000000000000) (11043546049633923 / 12500000000000000) ((ndm x c)^2) := bsq (lowGroupedE60C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (13956453950366077 / 12500000000000000) (1365749117533944219 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE60C_hz41 hx hc) (lowGroupedE60C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE60C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE60C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (13956453950366077 / 25000000000000000) (6851962236498971 / 10000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE60C_hz43 hx hc) (lowGroupedE60C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (13956453950366077 / 25000000000000000) (6851962236498971 / 10000000000000000) (nc1 x c) := by
    convert (lowGroupedE60C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE60C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (172132532159470679 / 250000000000000000) (344265064318941861 / 500000000000000000) (kdot ((13956453950366077 / 25000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (266216254324124243 / 500000000000000000)) (a := (489255729842892793 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (106486501729649697 / 200000000000000000)) (a := (244627864921445607 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE60C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (148056712200693993 / 200000000000000000) (740283561003469967 / 1000000000000000000) (kdot ((6851962236498971 / 10000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (432209917614544829 / 1000000000000000000)) (a := (12748800887000007 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (108052479403636207 / 250000000000000000)) (a := (203980814192000111 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE60C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (172132532159470679 / 250000000000000000) (740283561003469967 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE60C_hz47 hx hc) (lowGroupedE60C_hz48 hx hc).1 (lowGroupedE60C_hz49 hx hc).2

theorem lowGroupedE60C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE60C_hz51 hx hc) (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE60C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (172132532159470679 / 500000000000000000) (46267722562716873 / 125000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE60C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (172132532159470679 / 500000000000000000) (185370629721074537 / 500000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE60C_hz54 hx hc) (lowGroupedE60C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (352194011914975033 / 1000000000000000000) (17609700595748753 / 50000000000000000) ((kdot ((598881659 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE60C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (352194011914975033 / 1000000000000000000) (7055869817107783 / 20000000000000000) (((kdot ((598881659 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE60C_hz56 hx hc) (lowGroupedE60C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE60C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE60C_hz58 hx hc) (lowGroupedE60C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE60C_hz3 hx hc) (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE60C_hz60 hx hc) (lowGroupedE60C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE60C_hz4 hx hc) (lowGroupedE60C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE60C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE60C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (74182419994035547 / 125000000000000000) (593964216813933287 / 1000000000000000000) (√(((kdot ((598881659 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE60C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (74182419994035547 / 125000000000000000) (151286139175358059 / 250000000000000000) ((√(((kdot ((598881659 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE60C_hz65 hx hc) (lowGroupedE60C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (74182419994035547 / 125000000000000000) (9474117415347819 / 15625000000000000) (((√(((kdot ((598881659 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE60C_hz66 hx hc) (lowGroupedE60C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (167855655112355397 / 200000000000000000) (857499221779201209 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((598881659 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE60C_hz4 hx hc) (lowGroupedE60C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (167855655112355397 / 200000000000000000) (857499221779201209 / 1000000000000000000) (neb x (kdot (598881659 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE60C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE60C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE60C_hz4 hx hc) (lowGroupedE60C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE60C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE60C_hz3 hx hc) (lowGroupedE60C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE60C_hz71 hx hc) (lowGroupedE60C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE60C_hz4 hx hc) (lowGroupedE60C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE60C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE60C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE60C_hz4 hx hc) (lowGroupedE60C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE60C_hz76 hx hc) (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE60C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE60C_hz4 hx hc) (lowGroupedE60C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE60C_hz79 hx hc) (lowGroupedE60C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE60C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE60C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE60C_hz70 hx hc) (lowGroupedE60C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE60C_hz82 hx hc) (lowGroupedE60C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE60C_hz4 hx hc) (lowGroupedE60C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE60C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE60C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (586741053889142273 / 1000000000000000000) (608885259668970041 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE60C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (586741053889142273 / 500000000000000000) (608885259668970041 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE60C_hz70 hx hc) (lowGroupedE60C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (20714698103770517 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE60C_hz87 hx hc) (lowGroupedE60C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE60C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (840161999239631 / 40000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE60C_hz89 hx hc) (lowGroupedE60C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (840161999239631 / 20000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (840161999239631 / 20000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE60C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE60C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE60C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE60C_hz94 hx hc) (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE60C_hz96 hx hc) (lowGroupedE60C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE60C_hz97 hx hc) (lowGroupedE60C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE60C_hz98 hx hc) (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE60C_hz95 hx hc) (lowGroupedE60C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE60C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (43543091785649681 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE60C_hz93 hx hc) (lowGroupedE60C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (9084005289538817 / 200000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE60C_hz100 hx hc) (lowGroupedE60C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (172132532159470679 / 250000000000000000) (185370629721074537 / 250000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE60C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (704388023829950063 / 1000000000000000000) (367652457675967851 / 500000000000000000) ((neb x (kdot (598881659 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE60C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE60C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE60C_hz106 hx hc) (lowGroupedE60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (704388023829950063 / 1000000000000000000) (91952528170475979 / 125000000000000000) (((neb x (kdot (598881659 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE60C_hz105 hx hc) (lowGroupedE60C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (60624047082327439 / 125000000000000000) (545449537644991301 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (598881659 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE60C_hz104 hx hc) (lowGroupedE60C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (60624047082327439 / 125000000000000000) (295434782046342693 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (598881659 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE60C_hz103 hx hc) (lowGroupedE60C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE60C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) : B (60624047082327439 / 125000000000000000) (295434782046342693 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (598881659 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE60C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE60C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (26390681 / 62500000) (598881659 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (598881659 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (118173913 / 200000000) :=
  (lowGroupedE60C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE80W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE80W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (168328459 / 500000000) (69827511 / 100000000) c := hc

theorem lowGroupedE80W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE80W_hz2 hx hc) (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE80W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE80W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE80W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE80W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE80W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE80W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE80W_hz11 hx hc) (lowGroupedE80W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE80W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE80W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (24371850174142823 / 40000000000000000) (76162031908148143 / 125000000000000000) (kdot ((168328459 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (704464523109034549 / 1000000000000000000)) (a := (613716008526418921 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (176116130777258637 / 250000000000000000)) (a := (306858003547229053 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE80W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (28334470109314681 / 250000000000000000) (28334470109314681 / 250000000000000000) (((168328459 / 500000000) : ℝ)^2) := bsq (bpoint ((168328459 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (221665529890685319 / 250000000000000000) (221665529890685319 / 250000000000000000) ((1 : ℝ) - (((168328459 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE80W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (941627378299261897 / 1000000000000000000) (470813689149630949 / 500000000000000000) (√((1 : ℝ) - (((168328459 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE80W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (37466162951747407 / 125000000000000000) (299729303613979257 / 1000000000000000000) ((√((1 : ℝ) - (((168328459 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE80W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (1602529680778259 / 7812500000000000) (25640474930814813 / 125000000000000000) (((168328459 / 500000000) : ℝ) * (kdot ((168328459 / 500000000)))) := bmul (bpoint ((168328459 / 500000000) : ℝ)) (lowGroupedE80W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (63106637844199551 / 125000000000000000) (504853103060497761 / 1000000000000000000) (((√((1 : ℝ) - (((168328459 / 500000000) : ℝ)^2))) / Real.pi) + (((168328459 / 500000000) : ℝ) * (kdot ((168328459 / 500000000))))) := badd (lowGroupedE80W_hz18 hx hc) (lowGroupedE80W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (63106637844199551 / 125000000000000000) (504853103060497761 / 1000000000000000000) (kappa ((168328459 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE80W_hz20 hx hc)

theorem lowGroupedE80W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (9325609661987159 / 12500000000000000) (746048772958972723 / 1000000000000000000) (kdot ((69827511 / 100000000))) := by
    constructor
    · apply bkdot_lower (q := (210751925341019251 / 500000000000000000)) (a := (398905654621102473 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (421503850682038501 / 1000000000000000000)) (a := (398905654621102471 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE80W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (4875881292455121 / 10000000000000000) (4875881292455121 / 10000000000000000) (((69827511 / 100000000) : ℝ)^2) := bsq (bpoint ((69827511 / 100000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (5124118707544879 / 10000000000000000) (5124118707544879 / 10000000000000000) ((1 : ℝ) - (((69827511 / 100000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE80W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (715829498382462511 / 1000000000000000000) (44739343648903907 / 62500000000000000) (√((1 : ℝ) - (((69827511 / 100000000) : ℝ)^2))) := bsqrt (lowGroupedE80W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (22785560615712161 / 100000000000000000) (227855606157121611 / 1000000000000000000) ((√((1 : ℝ) - (((69827511 / 100000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE80W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (520947289003291701 / 1000000000000000000) (65118411125411463 / 125000000000000000) (((69827511 / 100000000) : ℝ) * (kdot ((69827511 / 100000000)))) := bmul (bpoint ((69827511 / 100000000) : ℝ)) (lowGroupedE80W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (748802895160413311 / 1000000000000000000) (149760579032082663 / 200000000000000000) (((√((1 : ℝ) - (((69827511 / 100000000) : ℝ)^2))) / Real.pi) + (((69827511 / 100000000) : ℝ) * (kdot ((69827511 / 100000000))))) := badd (lowGroupedE80W_hz26 hx hc) (lowGroupedE80W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (748802895160413311 / 1000000000000000000) (149760579032082663 / 200000000000000000) (kappa ((69827511 / 100000000))) := by rw [kappa_eq]; exact (lowGroupedE80W_hz28 hx hc)

theorem lowGroupedE80W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (63106637844199551 / 125000000000000000) (149760579032082663 / 200000000000000000) (kappa c) := bkappa (lowGroupedE80W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE80W_hz21 hx hc).1 (lowGroupedE80W_hz29 hx hc).2

theorem lowGroupedE80W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (50239420967917337 / 200000000000000000) (61893362155800449 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE80W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (50239420967917337 / 100000000000000000) (61893362155800449 / 62500000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE80W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (50239408467917337 / 100000000000000000) (61893362155800449 / 62500000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE80W_hz32 hx hc) (lowGroupedE80W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (44299852068353693 / 62500000000000000) (62195941465159349 / 62500000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE80W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE80W_hz36 hx hc) (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (705406468102096453 / 1000000000000000000) (62195941465159349 / 62500000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE80W_hz35 hx hc) (lowGroupedE80W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (705406468102096453 / 1000000000000000000) (62195941465159349 / 62500000000000000) (ndm x c) := by
    convert (lowGroupedE80W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE80W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE80W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE80W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (24879914262013701 / 50000000000000000) (495146897246403593 / 500000000000000000) ((ndm x c)^2) := bsq (lowGroupedE80W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (504853102753596407 / 500000000000000000) (754594897371425627 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE80W_hz41 hx hc) (lowGroupedE80W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE80W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE80W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (504853102753596407 / 1000000000000000000) (189290099999472229 / 250000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE80W_hz43 hx hc) (lowGroupedE80W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (504853102753596407 / 1000000000000000000) (189290099999472229 / 250000000000000000) (nc1 x c) := by
    convert (lowGroupedE80W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE80W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (668453341572876197 / 1000000000000000000) (167113335393228711 / 250000000000000000) (kdot ((504853102753596407 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (2294457238853247 / 4000000000000000)) (a := (260396136609224163 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (573614309713311749 / 1000000000000000000)) (a := (520792273218387621 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE80W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (193353472909960477 / 250000000000000000) (77341389163984191 / 100000000000000000) (kdot ((189290099999472229 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (185876315477738959 / 500000000000000000)) (a := (355920626714886747 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (371752630955477917 / 1000000000000000000)) (a := (71184125342977349 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE80W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (668453341572876197 / 1000000000000000000) (77341389163984191 / 100000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE80W_hz47 hx hc) (lowGroupedE80W_hz48 hx hc).1 (lowGroupedE80W_hz49 hx hc).2

theorem lowGroupedE80W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE80W_hz51 hx hc) (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE80W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (167113335393219049 / 500000000000000000) (77341389163984191 / 200000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE80W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (167113335393219049 / 500000000000000000) (77461284952067009 / 200000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE80W_hz54 hx hc) (lowGroupedE80W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (9325609661987159 / 25000000000000000) (186512193239743181 / 500000000000000000) ((kdot ((69827511 / 100000000))) / (2 : ℝ)) := bdiv (lowGroupedE80W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (9325609661987159 / 25000000000000000) (93405966354975113 / 250000000000000000) (((kdot ((69827511 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE80W_hz56 hx hc) (lowGroupedE80W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE80W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE80W_hz58 hx hc) (lowGroupedE80W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE80W_hz3 hx hc) (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE80W_hz60 hx hc) (lowGroupedE80W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE80W_hz4 hx hc) (lowGroupedE80W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE80W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE80W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (610757223845519783 / 1000000000000000000) (61124779379552811 / 100000000000000000) (√(((kdot ((69827511 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE80W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (610757223845519783 / 1000000000000000000) (622428133683027059 / 1000000000000000000) ((√(((kdot ((69827511 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE80W_hz65 hx hc) (lowGroupedE80W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (610757223845519783 / 1000000000000000000) (623627091563855239 / 1000000000000000000) (((√(((kdot ((69827511 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE80W_hz66 hx hc) (lowGroupedE80W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (172748229855934873 / 200000000000000000) (881941890752892049 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((69827511 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE80W_hz4 hx hc) (lowGroupedE80W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (172748229855934873 / 200000000000000000) (881941890752892049 / 1000000000000000000) (neb x (kdot (69827511 / 100000000)/2+√23*x)) := by
    convert (lowGroupedE80W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE80W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE80W_hz4 hx hc) (lowGroupedE80W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE80W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE80W_hz3 hx hc) (lowGroupedE80W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE80W_hz71 hx hc) (lowGroupedE80W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE80W_hz4 hx hc) (lowGroupedE80W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE80W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE80W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE80W_hz4 hx hc) (lowGroupedE80W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE80W_hz76 hx hc) (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE80W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE80W_hz4 hx hc) (lowGroupedE80W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE80W_hz79 hx hc) (lowGroupedE80W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE80W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE80W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE80W_hz70 hx hc) (lowGroupedE80W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE80W_hz82 hx hc) (lowGroupedE80W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE80W_hz4 hx hc) (lowGroupedE80W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE80W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE80W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (28906170223087237 / 50000000000000000) (155584869275649489 / 250000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE80W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (28906170223087237 / 25000000000000000) (155584869275649489 / 125000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE80W_hz70 hx hc) (lowGroupedE80W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (21172419896069461 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE80W_hz87 hx hc) (lowGroupedE80W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE80W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (21461771773289719 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE80W_hz89 hx hc) (lowGroupedE80W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (21461771773289719 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (21461771773289719 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE80W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE80W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE80W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE80W_hz94 hx hc) (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE80W_hz96 hx hc) (lowGroupedE80W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE80W_hz97 hx hc) (lowGroupedE80W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE80W_hz98 hx hc) (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE80W_hz95 hx hc) (lowGroupedE80W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE80W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (1779679440970247 / 40000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE80W_hz93 hx hc) (lowGroupedE80W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (46368920686300579 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE80W_hz100 hx hc) (lowGroupedE80W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (167113335393219049 / 250000000000000000) (77461284952067009 / 100000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (149209754591794543 / 200000000000000000) (388910749332393087 / 500000000000000000) ((neb x (kdot (69827511 / 100000000)/2+√23*x))^2) := bsq (lowGroupedE80W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE80W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE80W_hz106 hx hc) (lowGroupedE80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (149209754591794543 / 200000000000000000) (6079193817786393 / 7812500000000000) (((neb x (kdot (69827511 / 100000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE80W_hz105 hx hc) (lowGroupedE80W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (9973975905215387 / 20000000000000000) (602754770685946771 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (69827511 / 100000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE80W_hz104 hx hc) (lowGroupedE80W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (9973975905215387 / 20000000000000000) (12982473827444947 / 20000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (69827511 / 100000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE80W_hz103 hx hc) (lowGroupedE80W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) : B (9973975905215387 / 20000000000000000) (12982473827444947 / 20000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (69827511 / 100000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE80W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE80W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (168328459 / 500000000) (69827511 / 100000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (69827511 / 100000000)/2+√23*x)^2) (np1 x) ≤ (162280923 / 250000000) :=
  (lowGroupedE80W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE80C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE80C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (412270461 / 1000000000) (11780559 / 20000000) c := hc

theorem lowGroupedE80C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE80C_hz2 hx hc) (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE80C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE80C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE80C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE80C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE80C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE80C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE80C_hz11 hx hc) (lowGroupedE80C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE80C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE80C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (635264120167599831 / 1000000000000000000) (9926001877809467 / 15625000000000000) (kdot ((412270461 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (322552064480370419 / 500000000000000000)) (a := (286462890145519499 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (645104128960740837 / 1000000000000000000)) (a := (572925780271865771 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE80C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (169966933013152521 / 1000000000000000000) (169966933013152521 / 1000000000000000000) (((412270461 / 1000000000) : ℝ)^2) := bsq (bpoint ((412270461 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (830033066986847479 / 1000000000000000000) (830033066986847479 / 1000000000000000000) ((1 : ℝ) - (((412270461 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE80C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (911061505600388913 / 1000000000000000000) (455530752800194457 / 500000000000000000) (√((1 : ℝ) - (((412270461 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE80C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (144999942077046381 / 500000000000000000) (289999884154092763 / 1000000000000000000) ((√((1 : ℝ) - (((412270461 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE80C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (261900631678255779 / 1000000000000000000) (261900631683287977 / 1000000000000000000) (((412270461 / 1000000000) : ℝ) * (kdot ((412270461 / 1000000000)))) := bmul (bpoint ((412270461 / 1000000000) : ℝ)) (lowGroupedE80C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (551900515832348541 / 1000000000000000000) (27595025791869037 / 50000000000000000) (((√((1 : ℝ) - (((412270461 / 1000000000) : ℝ)^2))) / Real.pi) + (((412270461 / 1000000000) : ℝ) * (kdot ((412270461 / 1000000000))))) := badd (lowGroupedE80C_hz18 hx hc) (lowGroupedE80C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (551900515832348541 / 1000000000000000000) (27595025791869037 / 50000000000000000) (kappa ((412270461 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE80C_hz20 hx hc)

theorem lowGroupedE80C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (87561152005727549 / 125000000000000000) (1400978432091641 / 2000000000000000) (kdot ((11780559 / 20000000))) := by
    constructor
    · apply bkdot_lower (q := (101711573012116057 / 200000000000000000)) (a := (47047043927068519 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (127139466265145071 / 250000000000000000)) (a := (235235219635342511 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE80C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (138781570352481 / 400000000000000) (138781570352481 / 400000000000000) (((11780559 / 20000000) : ℝ)^2) := bsq (bpoint ((11780559 / 20000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (261218429647519 / 400000000000000) (261218429647519 / 400000000000000) ((1 : ℝ) - (((11780559 / 20000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE80C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (404056330886795257 / 500000000000000000) (161622532354718103 / 200000000000000000) (√((1 : ℝ) - (((11780559 / 20000000) : ℝ)^2))) := bsqrt (lowGroupedE80C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (257230249392831723 / 1000000000000000000) (64307562348207931 / 250000000000000000) ((√((1 : ℝ) - (((11780559 / 20000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE80C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (412607726924576691 / 1000000000000000000) (103151931731144189 / 250000000000000000) (((11780559 / 20000000) : ℝ) * (kdot ((11780559 / 20000000)))) := bmul (bpoint ((11780559 / 20000000) : ℝ)) (lowGroupedE80C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (334918988158704207 / 500000000000000000) (4186487351983803 / 6250000000000000) (((√((1 : ℝ) - (((11780559 / 20000000) : ℝ)^2))) / Real.pi) + (((11780559 / 20000000) : ℝ) * (kdot ((11780559 / 20000000))))) := badd (lowGroupedE80C_hz26 hx hc) (lowGroupedE80C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (334918988158704207 / 500000000000000000) (4186487351983803 / 6250000000000000) (kappa ((11780559 / 20000000))) := by rw [kappa_eq]; exact (lowGroupedE80C_hz28 hx hc)

theorem lowGroupedE80C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (551900515832348541 / 1000000000000000000) (4186487351983803 / 6250000000000000) (kappa c) := bkappa (lowGroupedE80C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE80C_hz21 hx hc).1 (lowGroupedE80C_hz29 hx hc).2

theorem lowGroupedE80C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (2063512648016197 / 6250000000000000) (448099484167651459 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE80C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (2063512648016197 / 3125000000000000) (448099484167651459 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE80C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (2063512257391197 / 3125000000000000) (448099484167651459 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE80C_hz32 hx hc) (lowGroupedE80C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (812603176442956713 / 1000000000000000000) (946677858796382181 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE80C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE80C_hz36 hx hc) (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (404606005725697039 / 500000000000000000) (946677858796382181 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE80C_hz35 hx hc) (lowGroupedE80C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (404606005725697039 / 500000000000000000) (946677858796382181 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE80C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE80C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE80C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE80C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (32741203973860557 / 50000000000000000) (22404974208382573 / 25000000000000000) ((ndm x c)^2) := bsq (lowGroupedE80C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (27595025791617427 / 25000000000000000) (675982000252957067 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE80C_hz41 hx hc) (lowGroupedE80C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE80C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE80C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (27595025791617427 / 50000000000000000) (678280231533253211 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE80C_hz43 hx hc) (lowGroupedE80C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (27595025791617427 / 50000000000000000) (678280231533253211 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE80C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE80C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (343048595113478741 / 500000000000000000) (343048595113479529 / 500000000000000000) (kdot ((27595025791617427 / 50000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (33584222660977393 / 62500000000000000)) (a := (493077380562092363 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (537347562575638287 / 1000000000000000000)) (a := (15408668142565309 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE80C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (737274444447032833 / 1000000000000000000) (184318611111758209 / 250000000000000000) (kdot ((678280231533253211 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (109457781830582659 / 250000000000000000)) (a := (412688337617749379 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (87566225464466127 / 200000000000000000)) (a := (412688337617749377 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE80C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (343048595113478741 / 500000000000000000) (184318611111758209 / 250000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE80C_hz47 hx hc) (lowGroupedE80C_hz48 hx hc).1 (lowGroupedE80C_hz49 hx hc).2

theorem lowGroupedE80C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE80C_hz51 hx hc) (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE80C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (343048595113478741 / 1000000000000000000) (184318611111758209 / 500000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE80C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (343048595113478741 / 1000000000000000000) (92309175290982627 / 250000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE80C_hz54 hx hc) (lowGroupedE80C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (87561152005727549 / 250000000000000000) (1400978432091641 / 4000000000000000) ((kdot ((11780559 / 20000000))) / (2 : ℝ)) := bdiv (lowGroupedE80C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (87561152005727549 / 250000000000000000) (17542204348166217 / 50000000000000000) (((kdot ((11780559 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE80C_hz56 hx hc) (lowGroupedE80C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE80C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE80C_hz58 hx hc) (lowGroupedE80C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE80C_hz3 hx hc) (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE80C_hz60 hx hc) (lowGroupedE80C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE80C_hz4 hx hc) (lowGroupedE80C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE80C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE80C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (295907336856874079 / 500000000000000000) (37020058275217311 / 62500000000000000) (√(((kdot ((11780559 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE80C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (295907336856874079 / 500000000000000000) (24140050891639037 / 40000000000000000) ((√(((kdot ((11780559 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE80C_hz65 hx hc) (lowGroupedE80C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (295907336856874079 / 500000000000000000) (120940046034360821 / 200000000000000000) (((√(((kdot ((11780559 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE80C_hz66 hx hc) (lowGroupedE80C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (418476168988695337 / 500000000000000000) (427587633339548809 / 500000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((11780559 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE80C_hz4 hx hc) (lowGroupedE80C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (418476168988695337 / 500000000000000000) (427587633339548809 / 500000000000000000) (neb x (kdot (11780559 / 20000000)/2+√23*x)) := by
    convert (lowGroupedE80C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE80C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE80C_hz4 hx hc) (lowGroupedE80C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE80C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE80C_hz3 hx hc) (lowGroupedE80C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE80C_hz71 hx hc) (lowGroupedE80C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE80C_hz4 hx hc) (lowGroupedE80C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE80C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE80C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE80C_hz4 hx hc) (lowGroupedE80C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE80C_hz76 hx hc) (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE80C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE80C_hz4 hx hc) (lowGroupedE80C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE80C_hz79 hx hc) (lowGroupedE80C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE80C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE80C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE80C_hz70 hx hc) (lowGroupedE80C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE80C_hz82 hx hc) (lowGroupedE80C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE80C_hz4 hx hc) (lowGroupedE80C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE80C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE80C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (292851752220077531 / 500000000000000000) (607648501326161841 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE80C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (292851752220077531 / 250000000000000000) (607648501326161841 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE80C_hz70 hx hc) (lowGroupedE80C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (4134524545732409 / 200000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE80C_hz87 hx hc) (lowGroupedE80C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE80C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (20961974605882303 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE80C_hz89 hx hc) (lowGroupedE80C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (20961974605882303 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (20961974605882303 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE80C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE80C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE80C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE80C_hz94 hx hc) (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE80C_hz96 hx hc) (lowGroupedE80C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE80C_hz97 hx hc) (lowGroupedE80C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE80C_hz98 hx hc) (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE80C_hz95 hx hc) (lowGroupedE80C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE80C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (1738234645410677 / 40000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE80C_hz93 hx hc) (lowGroupedE80C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (45332800797311329 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE80C_hz100 hx hc) (lowGroupedE80C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (343048595113478741 / 500000000000000000) (92309175290982627 / 125000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE80C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (700489216045820387 / 1000000000000000000) (731324736739665729 / 1000000000000000000) ((neb x (kdot (11780559 / 20000000)/2+√23*x))^2) := bsq (lowGroupedE80C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE80C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE80C_hz106 hx hc) (lowGroupedE80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (700489216045820387 / 1000000000000000000) (731640046751537859 / 1000000000000000000) (((neb x (kdot (11780559 / 20000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE80C_hz105 hx hc) (lowGroupedE80C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (480603682913321547 / 1000000000000000000) (540296714603923461 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (11780559 / 20000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE80C_hz104 hx hc) (lowGroupedE80C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (480603682913321547 / 1000000000000000000) (58562951540123479 / 100000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (11780559 / 20000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE80C_hz103 hx hc) (lowGroupedE80C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE80C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) : B (480603682913321547 / 1000000000000000000) (58562951540123479 / 100000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (11780559 / 20000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE80C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE80C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (412270461 / 1000000000) (11780559 / 20000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (11780559 / 20000000)/2+√23*x)^2) (np1 x) ≤ (146407379 / 250000000) :=
  (lowGroupedE80C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE100W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE100W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (326676107 / 1000000000) (344409047 / 500000000) c := hc

theorem lowGroupedE100W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE100W_hz2 hx hc) (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE100W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE100W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE100W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE100W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE100W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE100W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE100W_hz11 hx hc) (lowGroupedE100W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE100W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE100W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (75741078015431269 / 125000000000000000) (75741078212842767 / 125000000000000000) (kdot ((326676107 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (356204632598287181 / 500000000000000000)) (a := (309502934860947767 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (712409265196574361 / 1000000000000000000)) (a := (38687866702571843 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE100W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (106717278884675449 / 1000000000000000000) (106717278884675449 / 1000000000000000000) (((326676107 / 1000000000) : ℝ)^2) := bsq (bpoint ((326676107 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (893282721115324551 / 1000000000000000000) (893282721115324551 / 1000000000000000000) ((1 : ℝ) - (((326676107 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE100W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (118142043817715233 / 125000000000000000) (189027270108344373 / 200000000000000000) (√((1 : ℝ) - (((326676107 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE100W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (300846244169098769 / 1000000000000000000) (30084624416909877 / 100000000000000000) ((√((1 : ℝ) - (((326676107 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE100W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (197942404048514983 / 1000000000000000000) (197942404564431941 / 1000000000000000000) (((326676107 / 1000000000) : ℝ) * (kdot ((326676107 / 1000000000)))) := bmul (bpoint ((326676107 / 1000000000) : ℝ)) (lowGroupedE100W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (62348581027201719 / 125000000000000000) (498788648733530711 / 1000000000000000000) (((√((1 : ℝ) - (((326676107 / 1000000000) : ℝ)^2))) / Real.pi) + (((326676107 / 1000000000) : ℝ) * (kdot ((326676107 / 1000000000))))) := badd (lowGroupedE100W_hz18 hx hc) (lowGroupedE100W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (62348581027201719 / 125000000000000000) (498788648733530711 / 1000000000000000000) (kappa ((326676107 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE100W_hz20 hx hc)

theorem lowGroupedE100W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (741870130197794907 / 1000000000000000000) (741870130197794909 / 1000000000000000000) (kdot ((344409047 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (214627682373851383 / 500000000000000000)) (a := (405469451321348667 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (85851072949540553 / 200000000000000000)) (a := (202734725660674333 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE100W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (118617591655448209 / 250000000000000000) (118617591655448209 / 250000000000000000) (((344409047 / 500000000) : ℝ)^2) := bsq (bpoint ((344409047 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (131382408344551791 / 250000000000000000) (131382408344551791 / 250000000000000000) ((1 : ℝ) - (((344409047 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE100W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (28997369077299607 / 40000000000000000) (11327097295820159 / 15625000000000000) (√((1 : ℝ) - (((344409047 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE100W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (9230149250624609 / 40000000000000000) (230753731265615227 / 1000000000000000000) ((√((1 : ℝ) - (((344409047 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE100W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (51101356907837693 / 100000000000000000) (511013569078376933 / 1000000000000000000) (((344409047 / 500000000) : ℝ) * (kdot ((344409047 / 500000000)))) := bmul (bpoint ((344409047 / 500000000) : ℝ)) (lowGroupedE100W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (148353460068798431 / 200000000000000000) (4636045627149951 / 6250000000000000) (((√((1 : ℝ) - (((344409047 / 500000000) : ℝ)^2))) / Real.pi) + (((344409047 / 500000000) : ℝ) * (kdot ((344409047 / 500000000))))) := badd (lowGroupedE100W_hz26 hx hc) (lowGroupedE100W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (148353460068798431 / 200000000000000000) (4636045627149951 / 6250000000000000) (kappa ((344409047 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE100W_hz28 hx hc)

theorem lowGroupedE100W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (62348581027201719 / 125000000000000000) (4636045627149951 / 6250000000000000) (kappa c) := bkappa (lowGroupedE100W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE100W_hz21 hx hc).1 (lowGroupedE100W_hz29 hx hc).2

theorem lowGroupedE100W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1613954372850049 / 6250000000000000) (62651418972798281 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE100W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1613954372850049 / 3125000000000000) (62651418972798281 / 62500000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE100W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1613953982225049 / 3125000000000000) (62651418972798281 / 62500000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE100W_hz32 hx hc) (lowGroupedE100W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (143731036914372211 / 200000000000000000) (62575663686451561 / 62500000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE100W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE100W_hz36 hx hc) (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (35763200979014921 / 50000000000000000) (62575663686451561 / 62500000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE100W_hz35 hx hc) (lowGroupedE100W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (35763200979014921 / 50000000000000000) (62575663686451561 / 62500000000000000) (ndm x c) := by
    convert (lowGroupedE100W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE100W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE100W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE100W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (511602617706165521 / 1000000000000000000) (1002422703564772497 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE100W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (997577296435227503 / 1000000000000000000) (1495185462276959753 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE100W_hz41 hx hc) (lowGroupedE100W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE100W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE100W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (498788648217613751 / 1000000000000000000) (375067213756751987 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE100W_hz43 hx hc) (lowGroupedE100W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (498788648217613751 / 1000000000000000000) (375067213756751987 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE100W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE100W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (666221610662204637 / 1000000000000000000) (666221610662262129 / 1000000000000000000) (kdot ((498788648217613751 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (115656553766827713 / 200000000000000000)) (a := (524297867935325841 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (144570692208534641 / 250000000000000000)) (a := (104859573587047107 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE100W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (770011243097889013 / 1000000000000000000) (96251405387236127 / 125000000000000000) (kdot ((375067213756751987 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (377848329629306077 / 1000000000000000000)) (a := (90316373636490091 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (94462082407326519 / 250000000000000000)) (a := (180632747272980181 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE100W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (666221610662204637 / 1000000000000000000) (96251405387236127 / 125000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE100W_hz47 hx hc) (lowGroupedE100W_hz48 hx hc).1 (lowGroupedE100W_hz49 hx hc).2

theorem lowGroupedE100W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE100W_hz51 hx hc) (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE100W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (166555402665551159 / 500000000000000000) (96251405387236127 / 250000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE100W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (166555402665551159 / 500000000000000000) (192802550244679299 / 500000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE100W_hz54 hx hc) (lowGroupedE100W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (370935065098897453 / 1000000000000000000) (74187013019779491 / 200000000000000000) ((kdot ((344409047 / 500000000))) / (2 : ℝ)) := bdiv (lowGroupedE100W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (370935065098897453 / 1000000000000000000) (74306908807862309 / 200000000000000000) (((kdot ((344409047 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE100W_hz56 hx hc) (lowGroupedE100W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE100W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE100W_hz58 hx hc) (lowGroupedE100W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE100W_hz3 hx hc) (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE100W_hz60 hx hc) (lowGroupedE100W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE100W_hz4 hx hc) (lowGroupedE100W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE100W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE100W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (121808877361035957 / 200000000000000000) (152384083822612431 / 250000000000000000) (√(((kdot ((344409047 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE100W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (121808877361035957 / 200000000000000000) (620716675177948673 / 1000000000000000000) ((√(((kdot ((344409047 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE100W_hz65 hx hc) (lowGroupedE100W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (121808877361035957 / 200000000000000000) (621915633058776853 / 1000000000000000000) (((√(((kdot ((344409047 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE100W_hz66 hx hc) (lowGroupedE100W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (215329707976772637 / 250000000000000000) (879521522923571413 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((344409047 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE100W_hz4 hx hc) (lowGroupedE100W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (215329707976772637 / 250000000000000000) (879521522923571413 / 1000000000000000000) (neb x (kdot (344409047 / 500000000)/2+√23*x)) := by
    convert (lowGroupedE100W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE100W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE100W_hz4 hx hc) (lowGroupedE100W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE100W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE100W_hz3 hx hc) (lowGroupedE100W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE100W_hz71 hx hc) (lowGroupedE100W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE100W_hz4 hx hc) (lowGroupedE100W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE100W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE100W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE100W_hz4 hx hc) (lowGroupedE100W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE100W_hz76 hx hc) (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE100W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE100W_hz4 hx hc) (lowGroupedE100W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE100W_hz79 hx hc) (lowGroupedE100W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE100W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE100W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE100W_hz70 hx hc) (lowGroupedE100W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE100W_hz82 hx hc) (lowGroupedE100W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE100W_hz4 hx hc) (lowGroupedE100W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE100W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE100W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (18036172566017287 / 31250000000000000) (77621386841167867 / 125000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE100W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (18036172566017287 / 15625000000000000) (77621386841167867 / 62500000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE100W_hz70 hx hc) (lowGroupedE100W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (10562933290156767 / 500000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE100W_hz87 hx hc) (lowGroupedE100W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE100W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (669225576797931 / 31250000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE100W_hz89 hx hc) (lowGroupedE100W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (669225576797931 / 15625000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (669225576797931 / 15625000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE100W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE100W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE100W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE100W_hz94 hx hc) (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE100W_hz96 hx hc) (lowGroupedE100W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE100W_hz97 hx hc) (lowGroupedE100W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE100W_hz98 hx hc) (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE100W_hz95 hx hc) (lowGroupedE100W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE100W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (34683966594763 / 781250000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE100W_hz93 hx hc) (lowGroupedE100W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (11568102975835261 / 250000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE100W_hz100 hx hc) (lowGroupedE100W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (166555402665551159 / 250000000000000000) (192802550244679299 / 250000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (370935065098897451 / 500000000000000000) (154711621857159671 / 200000000000000000) ((neb x (kdot (344409047 / 500000000)/2+√23*x))^2) := bsq (lowGroupedE100W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE100W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE100W_hz106 hx hc) (lowGroupedE100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (370935065098897451 / 500000000000000000) (154774683859534097 / 200000000000000000) (((neb x (kdot (344409047 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE100W_hz105 hx hc) (lowGroupedE100W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (494249913042554377 / 1000000000000000000) (298409537614321769 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (344409047 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE100W_hz104 hx hc) (lowGroupedE100W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (494249913042554377 / 1000000000000000000) (321545743565992291 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (344409047 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE100W_hz103 hx hc) (lowGroupedE100W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) : B (494249913042554377 / 1000000000000000000) (321545743565992291 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (344409047 / 500000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE100W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE100W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (326676107 / 1000000000) (344409047 / 500000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (344409047 / 500000000)/2+√23*x)^2) (np1 x) ≤ (20096609 / 31250000) :=
  (lowGroupedE100W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE100C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE100C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (20115947 / 50000000) (579139237 / 1000000000) c := hc

theorem lowGroupedE100C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE100C_hz2 hx hc) (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE100C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE100C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE100C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE100C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE100C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE100C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE100C_hz11 hx hc) (lowGroupedE100C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE100C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE100C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (25271828195639067 / 40000000000000000) (19743615778527437 / 31250000000000000) (kdot ((20115947 / 50000000))) := by
    constructor
    · apply bkdot_lower (q := (163211725266594531 / 250000000000000000)) (a := (578373954267357957 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (652846901066378123 / 1000000000000000000)) (a := (289186977116477731 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE100C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (404651323706809 / 2500000000000000) (404651323706809 / 2500000000000000) (((20115947 / 50000000) : ℝ)^2) := bsq (bpoint ((20115947 / 50000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (2095348676293191 / 2500000000000000) (2095348676293191 / 2500000000000000) ((1 : ℝ) - (((20115947 / 50000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE100C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (915499574285688239 / 1000000000000000000) (11443744678571103 / 12500000000000000) (√((1 : ℝ) - (((20115947 / 50000000) : ℝ)^2))) := bsqrt (lowGroupedE100C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (72853141323046559 / 250000000000000000) (291412565292186237 / 1000000000000000000) ((√((1 : ℝ) - (((20115947 / 50000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE100C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (254183378288290551 / 1000000000000000000) (254183378297101863 / 1000000000000000000) (((20115947 / 50000000) : ℝ) * (kdot ((20115947 / 50000000)))) := bmul (bpoint ((20115947 / 50000000) : ℝ)) (lowGroupedE100C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (545595943580476787 / 1000000000000000000) (5455959435892881 / 10000000000000000) (((√((1 : ℝ) - (((20115947 / 50000000) : ℝ)^2))) / Real.pi) + (((20115947 / 50000000) : ℝ) * (kdot ((20115947 / 50000000))))) := badd (lowGroupedE100C_hz18 hx hc) (lowGroupedE100C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (545595943580476787 / 1000000000000000000) (5455959435892881 / 10000000000000000) (kappa ((20115947 / 50000000))) := by rw [kappa_eq]; exact (lowGroupedE100C_hz20 hx hc)

theorem lowGroupedE100C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (174152810977959081 / 250000000000000000) (696611243911836547 / 1000000000000000000) (kdot ((579139237 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (51624874249786551 / 100000000000000000)) (a := (47656194365416033 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (516248742497865509 / 1000000000000000000)) (a := (476561943654159981 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE100C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (335402255832942169 / 1000000000000000000) (335402255832942169 / 1000000000000000000) (((579139237 / 1000000000) : ℝ)^2) := bsq (bpoint ((579139237 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (664597744167057831 / 1000000000000000000) (664597744167057831 / 1000000000000000000) ((1 : ℝ) - (((579139237 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE100C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (407614322665144407 / 500000000000000000) (163045729066057763 / 200000000000000000) (√((1 : ℝ) - (((579139237 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE100C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (64873834327212521 / 250000000000000000) (129747668654425043 / 500000000000000000) ((√((1 : ℝ) - (((579139237 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE100C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (403434904284721783 / 1000000000000000000) (201717452142360957 / 500000000000000000) (((579139237 / 1000000000) : ℝ) * (kdot ((579139237 / 1000000000)))) := bmul (bpoint ((579139237 / 1000000000) : ℝ)) (lowGroupedE100C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (662930241593571867 / 1000000000000000000) (165732560398393 / 250000000000000) (((√((1 : ℝ) - (((579139237 / 1000000000) : ℝ)^2))) / Real.pi) + (((579139237 / 1000000000) : ℝ) * (kdot ((579139237 / 1000000000))))) := badd (lowGroupedE100C_hz26 hx hc) (lowGroupedE100C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (662930241593571867 / 1000000000000000000) (165732560398393 / 250000000000000) (kappa ((579139237 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE100C_hz28 hx hc)

theorem lowGroupedE100C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (545595943580476787 / 1000000000000000000) (165732560398393 / 250000000000000) (kappa c) := bkappa (lowGroupedE100C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE100C_hz21 hx hc).1 (lowGroupedE100C_hz29 hx hc).2

theorem lowGroupedE100C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (84267439601607 / 250000000000000) (454404056419523213 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE100C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (84267439601607 / 125000000000000) (454404056419523213 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE100C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (84267423976607 / 125000000000000) (454404056419523213 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE100C_hz32 hx hc) (lowGroupedE100C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (821059919745724769 / 1000000000000000000) (238328569526274801 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE100C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE100C_hz36 hx hc) (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (408834377377081067 / 500000000000000000) (238328569526274801 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE100C_hz35 hx hc) (lowGroupedE100C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (408834377377081067 / 500000000000000000) (238328569526274801 / 250000000000000000) (ndm x c) := by
    convert (lowGroupedE100C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE100C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE100C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE100C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (668582192501222141 / 1000000000000000000) (227202028209761607 / 250000000000000000) ((ndm x c)^2) := bsq (lowGroupedE100C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (272797971790238393 / 250000000000000000) (1338205887481903133 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE100C_hz41 hx hc) (lowGroupedE100C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE100C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE100C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (272797971790238393 / 500000000000000000) (67137778732327809 / 100000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE100C_hz43 hx hc) (lowGroupedE100C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (272797971790238393 / 500000000000000000) (67137778732327809 / 100000000000000000) (nc1 x c) := by
    convert (lowGroupedE100C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE100C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (683696654122572211 / 1000000000000000000) (683696654122574663 / 1000000000000000000) (kdot ((272797971790238393 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (542216981759026941 / 1000000000000000000)) (a := (496848133857199277 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (27110849087951347 / 50000000000000000)) (a := (248424066928597713 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE100C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (734297179717258499 / 1000000000000000000) (367148589858629251 / 500000000000000000) (kdot ((67137778732327809 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (221707890135548237 / 500000000000000000)) (a := (417365014119174903 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (443415780271096473 / 1000000000000000000)) (a := (417365014119174901 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE100C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (683696654122572211 / 1000000000000000000) (367148589858629251 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE100C_hz47 hx hc) (lowGroupedE100C_hz48 hx hc).1 (lowGroupedE100C_hz49 hx hc).2

theorem lowGroupedE100C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE100C_hz51 hx hc) (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE100C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (68369665412257221 / 200000000000000000) (367148589858629251 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE100C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (68369665412257221 / 200000000000000000) (367748068799043341 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE100C_hz54 hx hc) (lowGroupedE100C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (174152810977959081 / 500000000000000000) (174152810977959137 / 500000000000000000) ((kdot ((579139237 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE100C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (174152810977959081 / 500000000000000000) (87226275224083091 / 250000000000000000) (((kdot ((579139237 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE100C_hz56 hx hc) (lowGroupedE100C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE100C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE100C_hz58 hx hc) (lowGroupedE100C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE100C_hz3 hx hc) (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE100C_hz60 hx hc) (lowGroupedE100C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE100C_hz4 hx hc) (lowGroupedE100C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE100C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE100C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (590174230169293449 / 1000000000000000000) (590681894843859561 / 1000000000000000000) (√(((kdot ((579139237 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE100C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (590174230169293449 / 1000000000000000000) (60186223473135851 / 100000000000000000) ((√(((kdot ((579139237 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE100C_hz65 hx hc) (lowGroupedE100C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (590174230169293449 / 1000000000000000000) (60306119261218669 / 100000000000000000) (((√(((kdot ((579139237 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE100C_hz66 hx hc) (lowGroupedE100C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (417316200234257717 / 500000000000000000) (852857317533047769 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((579139237 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE100C_hz4 hx hc) (lowGroupedE100C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (417316200234257717 / 500000000000000000) (852857317533047769 / 1000000000000000000) (neb x (kdot (579139237 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE100C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE100C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE100C_hz4 hx hc) (lowGroupedE100C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE100C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE100C_hz3 hx hc) (lowGroupedE100C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE100C_hz71 hx hc) (lowGroupedE100C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE100C_hz4 hx hc) (lowGroupedE100C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE100C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE100C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE100C_hz4 hx hc) (lowGroupedE100C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE100C_hz76 hx hc) (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE100C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE100C_hz4 hx hc) (lowGroupedE100C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE100C_hz79 hx hc) (lowGroupedE100C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE100C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE100C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE100C_hz70 hx hc) (lowGroupedE100C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE100C_hz82 hx hc) (lowGroupedE100C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE100C_hz4 hx hc) (lowGroupedE100C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE100C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE100C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (292338984340647811 / 500000000000000000) (303211175915006199 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE100C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (292338984340647811 / 250000000000000000) (303211175915006199 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE100C_hz70 hx hc) (lowGroupedE100C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (20630908273862081 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE100C_hz87 hx hc) (lowGroupedE100C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE100C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (20920260151082339 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE100C_hz89 hx hc) (lowGroupedE100C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (20920260151082339 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (20920260151082339 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE100C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE100C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE100C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE100C_hz94 hx hc) (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE100C_hz96 hx hc) (lowGroupedE100C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE100C_hz97 hx hc) (lowGroupedE100C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE100C_hz98 hx hc) (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE100C_hz95 hx hc) (lowGroupedE100C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE100C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (8673877740365941 / 200000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE100C_hz93 hx hc) (lowGroupedE100C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (45246323363874109 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE100C_hz100 hx hc) (lowGroupedE100C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (68369665412257221 / 100000000000000000) (367748068799043341 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE100C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (348305621955918161 / 500000000000000000) (72736560406966587 / 100000000000000000) ((neb x (kdot (579139237 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE100C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE100C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE100C_hz106 hx hc) (lowGroupedE100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (348305621955918161 / 500000000000000000) (363840457040769 / 500000000000000) (((neb x (kdot (579139237 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE100C_hz105 hx hc) (lowGroupedE100C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (59533847085835693 / 125000000000000000) (267603250855408183 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (579139237 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE100C_hz104 hx hc) (lowGroupedE100C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (59533847085835693 / 125000000000000000) (23218113002987619 / 40000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (579139237 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE100C_hz103 hx hc) (lowGroupedE100C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE100C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) : B (59533847085835693 / 125000000000000000) (23218113002987619 / 40000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (579139237 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE100C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE100C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (20115947 / 50000000) (579139237 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (579139237 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (290226413 / 500000000) :=
  (lowGroupedE100C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE120W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE120W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (316744807 / 1000000000) (339644381 / 500000000) c := hc

theorem lowGroupedE120W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE120W_hz2 hx hc) (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE120W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE120W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE120W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE120W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE120W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE120W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE120W_hz11 hx hc) (lowGroupedE120W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE120W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE120W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (602589879436013591 / 1000000000000000000) (120517976430749019 / 200000000000000000) (kdot ((316744807 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (720345194781959181 / 1000000000000000000)) (a := (624250357613026859 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (36017259739097959 / 50000000000000000)) (a := (312125176672012099 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE120W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (100327272761467249 / 1000000000000000000) (100327272761467249 / 1000000000000000000) (((316744807 / 1000000000) : ℝ)^2) := bsq (bpoint ((316744807 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (899672727238532751 / 1000000000000000000) (899672727238532751 / 1000000000000000000) ((1 : ℝ) - (((316744807 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE120W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (118563849309568531 / 125000000000000000) (948510794476548249 / 1000000000000000000) (√((1 : ℝ) - (((316744807 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE120W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (150960181516963469 / 500000000000000000) (301920363033926939 / 1000000000000000000) ((√((1 : ℝ) - (((316744807 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE120W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (190867215062113393 / 1000000000000000000) (38173443184588147 / 200000000000000000) (((316744807 / 1000000000) : ℝ) * (kdot ((316744807 / 1000000000)))) := bmul (bpoint ((316744807 / 1000000000) : ℝ)) (lowGroupedE120W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (492787578096040331 / 1000000000000000000) (246393789478433837 / 500000000000000000) (((√((1 : ℝ) - (((316744807 / 1000000000) : ℝ)^2))) / Real.pi) + (((316744807 / 1000000000) : ℝ) * (kdot ((316744807 / 1000000000))))) := badd (lowGroupedE120W_hz18 hx hc) (lowGroupedE120W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (492787578096040331 / 1000000000000000000) (246393789478433837 / 500000000000000000) (kappa ((316744807 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE120W_hz20 hx hc)

theorem lowGroupedE120W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (368855803798862677 / 500000000000000000) (737711607597725357 / 1000000000000000000) (kdot ((339644381 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (437013042273712741 / 1000000000000000000)) (a := (412001643346431483 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (21850652113685637 / 50000000000000000)) (a := (412001643346431481 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE120W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (115358305544873161 / 250000000000000000) (115358305544873161 / 250000000000000000) (((339644381 / 500000000) : ℝ)^2) := bsq (bpoint ((339644381 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (134641694455126839 / 250000000000000000) (134641694455126839 / 250000000000000000) ((1 : ℝ) - (((339644381 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE120W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (183467772684419183 / 250000000000000000) (733871090737676733 / 1000000000000000000) (√((1 : ℝ) - (((339644381 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE120W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (233598423366284197 / 1000000000000000000) (116799211683142099 / 500000000000000000) ((√((1 : ℝ) - (((339644381 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE120W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (501119204638088649 / 1000000000000000000) (125279801159522163 / 250000000000000000) (((339644381 / 500000000) : ℝ) * (kdot ((339644381 / 500000000)))) := bmul (bpoint ((339644381 / 500000000) : ℝ)) (lowGroupedE120W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (367358814002186423 / 500000000000000000) (14694352560087457 / 20000000000000000) (((√((1 : ℝ) - (((339644381 / 500000000) : ℝ)^2))) / Real.pi) + (((339644381 / 500000000) : ℝ) * (kdot ((339644381 / 500000000))))) := badd (lowGroupedE120W_hz26 hx hc) (lowGroupedE120W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (367358814002186423 / 500000000000000000) (14694352560087457 / 20000000000000000) (kappa ((339644381 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE120W_hz28 hx hc)

theorem lowGroupedE120W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (492787578096040331 / 1000000000000000000) (14694352560087457 / 20000000000000000) (kappa c) := bkappa (lowGroupedE120W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE120W_hz21 hx hc).1 (lowGroupedE120W_hz29 hx hc).2

theorem lowGroupedE120W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (5305647439912543 / 20000000000000000) (507212421903959669 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE120W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (5305647439912543 / 10000000000000000) (507212421903959669 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE120W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (5305646189912543 / 10000000000000000) (507212421903959669 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE120W_hz32 hx hc) (lowGroupedE120W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (728398667620455151 / 1000000000000000000) (251796649576587811 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE120W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE120W_hz36 hx hc) (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (181251875657223129 / 250000000000000000) (251796649576587811 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE120W_hz35 hx hc) (lowGroupedE120W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (181251875657223129 / 250000000000000000) (251796649576587811 / 250000000000000000) (ndm x c) := by
    convert (lowGroupedE120W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE120W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE120W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE120W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (131408969717045897 / 250000000000000000) (1014424843807919339 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE120W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (985575156192080661 / 1000000000000000000) (740576100557470843 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE120W_hz41 hx hc) (lowGroupedE120W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE120W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE120W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (49278757809604033 / 100000000000000000) (743093941504573009 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE120W_hz43 hx hc) (lowGroupedE120W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (49278757809604033 / 100000000000000000) (743093941504573009 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE120W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE120W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (166005508682605421 / 250000000000000000) (664022034730506587 / 1000000000000000000) (kdot ((49278757809604033 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (145725630478580543 / 250000000000000000)) (a := (527752953729476967 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (582902521914322171 / 1000000000000000000)) (a := (527752953729343603 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE120W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (766642461843943207 / 1000000000000000000) (95830307730492901 / 125000000000000000) (kdot ((743093941504573009 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (191953829475614921 / 500000000000000000)) (a := (366557163765433943 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (383907658951229841 / 1000000000000000000)) (a := (183278581882716971 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE120W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (166005508682605421 / 250000000000000000) (95830307730492901 / 125000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE120W_hz47 hx hc) (lowGroupedE120W_hz48 hx hc).1 (lowGroupedE120W_hz49 hx hc).2

theorem lowGroupedE120W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE120W_hz51 hx hc) (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE120W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (166005508682605421 / 500000000000000000) (95830307730492901 / 250000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE120W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (166005508682605421 / 500000000000000000) (191960354931192847 / 500000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE120W_hz54 hx hc) (lowGroupedE120W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (368855803798862677 / 1000000000000000000) (368855803798862679 / 1000000000000000000) ((kdot ((339644381 / 500000000))) / (2 : ℝ)) := bdiv (lowGroupedE120W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (368855803798862677 / 1000000000000000000) (369455282739276769 / 1000000000000000000) (((kdot ((339644381 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE120W_hz56 hx hc) (lowGroupedE120W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE120W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE120W_hz58 hx hc) (lowGroupedE120W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE120W_hz3 hx hc) (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE120W_hz60 hx hc) (lowGroupedE120W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE120W_hz4 hx hc) (lowGroupedE120W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE120W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE120W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (151833750323928037 / 250000000000000000) (607828333281097361 / 1000000000000000000) (√(((kdot ((339644381 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE120W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (151833750323928037 / 250000000000000000) (61900867316859631 / 100000000000000000) ((√(((kdot ((339644381 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE120W_hz65 hx hc) (lowGroupedE120W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (151833750323928037 / 250000000000000000) (62020763104942449 / 100000000000000000) (((√(((kdot ((339644381 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE120W_hz66 hx hc) (lowGroupedE120W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (858901395736277373 / 1000000000000000000) (877106043317384803 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((339644381 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE120W_hz4 hx hc) (lowGroupedE120W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (858901395736277373 / 1000000000000000000) (877106043317384803 / 1000000000000000000) (neb x (kdot (339644381 / 500000000)/2+√23*x)) := by
    convert (lowGroupedE120W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE120W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE120W_hz4 hx hc) (lowGroupedE120W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE120W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE120W_hz3 hx hc) (lowGroupedE120W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE120W_hz71 hx hc) (lowGroupedE120W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE120W_hz4 hx hc) (lowGroupedE120W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE120W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE120W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE120W_hz4 hx hc) (lowGroupedE120W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE120W_hz76 hx hc) (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE120W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE120W_hz4 hx hc) (lowGroupedE120W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE120W_hz79 hx hc) (lowGroupedE120W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE120W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE120W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE120W_hz70 hx hc) (lowGroupedE120W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE120W_hz82 hx hc) (lowGroupedE120W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE120W_hz4 hx hc) (lowGroupedE120W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE120W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE120W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (23048158880577367 / 40000000000000000) (154903338783898089 / 250000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE120W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (23048158880577367 / 20000000000000000) (154903338783898089 / 125000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE120W_hz70 hx hc) (lowGroupedE120W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (21079675339285019 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE120W_hz87 hx hc) (lowGroupedE120W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE120W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (21369027216505277 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE120W_hz89 hx hc) (lowGroupedE120W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (21369027216505277 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (21369027216505277 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE120W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE120W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE120W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE120W_hz94 hx hc) (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE120W_hz96 hx hc) (lowGroupedE120W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE120W_hz97 hx hc) (lowGroupedE120W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE120W_hz98 hx hc) (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE120W_hz95 hx hc) (lowGroupedE120W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE120W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (8859943813697251 / 200000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE120W_hz93 hx hc) (lowGroupedE120W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (46176653730530659 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE120W_hz100 hx hc) (lowGroupedE120W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (166005508682605421 / 250000000000000000) (191960354931192847 / 250000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (737711607597725351 / 1000000000000000000) (769315011223878107 / 1000000000000000000) ((neb x (kdot (339644381 / 500000000)/2+√23*x))^2) := bsq (lowGroupedE120W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE120W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE120W_hz106 hx hc) (lowGroupedE120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (737711607597725351 / 1000000000000000000) (769630321235750237 / 1000000000000000000) (((neb x (kdot (339644381 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE120W_hz105 hx hc) (lowGroupedE120W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (122464190680322999 / 250000000000000000) (147738509630222583 / 250000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (339644381 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE120W_hz104 hx hc) (lowGroupedE120W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (122464190680322999 / 250000000000000000) (637130692251420991 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (339644381 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE120W_hz103 hx hc) (lowGroupedE120W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) : B (122464190680322999 / 250000000000000000) (637130692251420991 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (339644381 / 500000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE120W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE120W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (316744807 / 1000000000) (339644381 / 500000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (339644381 / 500000000)/2+√23*x)^2) (np1 x) ≤ (637130693 / 1000000000) :=
  (lowGroupedE120W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE120C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE120C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (392395949 / 1000000000) (284607923 / 500000000) c := hc

theorem lowGroupedE120C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE120C_hz2 hx hc) (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE120C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE120C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE120C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE120C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE120C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE120C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE120C_hz11 hx hc) (lowGroupedE120C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE120C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE120C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (314176846458962991 / 500000000000000000) (628353692956941093 / 1000000000000000000) (kdot ((392395949 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (26423415024004753 / 40000000000000000)) (a := (14594516350785251 / 25000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (82573171950014853 / 125000000000000000)) (a := (583780653970125249 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE120C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (153974580791610601 / 1000000000000000000) (153974580791610601 / 1000000000000000000) (((392395949 / 1000000000) : ℝ)^2) := bsq (bpoint ((392395949 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (846025419208389399 / 1000000000000000000) (846025419208389399 / 1000000000000000000) ((1 : ℝ) - (((392395949 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE120C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (183959280190849779 / 200000000000000000) (14371818764910139 / 15625000000000000) (√((1 : ℝ) - (((392395949 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE120C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (58556057540001451 / 200000000000000000) (36597535962500907 / 125000000000000000) ((√((1 : ℝ) - (((392395949 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE120C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (15410215227511509 / 62500000000000000) (246563443655493517 / 1000000000000000000) (((392395949 / 1000000000) : ℝ) * (kdot ((392395949 / 1000000000)))) := bmul (bpoint ((392395949 / 1000000000) : ℝ)) (lowGroupedE120C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (539343731340191399 / 1000000000000000000) (539343731355500773 / 1000000000000000000) (((√((1 : ℝ) - (((392395949 / 1000000000) : ℝ)^2))) / Real.pi) + (((392395949 / 1000000000) : ℝ) * (kdot ((392395949 / 1000000000))))) := badd (lowGroupedE120C_hz18 hx hc) (lowGroupedE120C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (539343731340191399 / 1000000000000000000) (539343731355500773 / 1000000000000000000) (kappa ((392395949 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE120C_hz20 hx hc)

theorem lowGroupedE120C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (346376562209331757 / 500000000000000000) (346376562209331987 / 500000000000000000) (kdot ((284607923 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (32746774918739463 / 62500000000000000)) (a := (3770486434237281 / 7812500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (523948398699831407 / 1000000000000000000)) (a := (30163891473898203 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE120C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (81001669834373929 / 250000000000000000) (81001669834373929 / 250000000000000000) (((284607923 / 500000000) : ℝ)^2) := bsq (bpoint ((284607923 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (168998330165626071 / 250000000000000000) (168998330165626071 / 250000000000000000) ((1 : ℝ) - (((284607923 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE120C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (822188129726101241 / 1000000000000000000) (411094064863050621 / 500000000000000000) (√((1 : ℝ) - (((284607923 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE120C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (52342121998955801 / 200000000000000000) (261710609994779007 / 1000000000000000000) ((√((1 : ℝ) - (((284607923 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE120C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (39432605578511281 / 100000000000000000) (394326055785113073 / 1000000000000000000) (((284607923 / 500000000) : ℝ) * (kdot ((284607923 / 500000000)))) := bmul (bpoint ((284607923 / 500000000) : ℝ)) (lowGroupedE120C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (131207333155978363 / 200000000000000000) (8200458322248651 / 12500000000000000) (((√((1 : ℝ) - (((284607923 / 500000000) : ℝ)^2))) / Real.pi) + (((284607923 / 500000000) : ℝ) * (kdot ((284607923 / 500000000))))) := badd (lowGroupedE120C_hz26 hx hc) (lowGroupedE120C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (131207333155978363 / 200000000000000000) (8200458322248651 / 12500000000000000) (kappa ((284607923 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE120C_hz28 hx hc)

theorem lowGroupedE120C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (539343731340191399 / 1000000000000000000) (8200458322248651 / 12500000000000000) (kappa c) := bkappa (lowGroupedE120C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE120C_hz21 hx hc).1 (lowGroupedE120C_hz29 hx hc).2

theorem lowGroupedE120C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (4299541677751349 / 12500000000000000) (460656268659808601 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE120C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (4299541677751349 / 6250000000000000) (460656268659808601 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE120C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (4299540896501349 / 6250000000000000) (460656268659808601 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE120C_hz32 hx hc) (lowGroupedE120C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (207353343269438243 / 250000000000000000) (191970053635416501 / 200000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE120C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE120C_hz36 hx hc) (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (826022208086190337 / 1000000000000000000) (191970053635416501 / 200000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE120C_hz35 hx hc) (lowGroupedE120C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (826022208086190337 / 1000000000000000000) (191970053635416501 / 200000000000000000) (ndm x c) := by
    convert (lowGroupedE120C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE120C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE120C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE120C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (85289086031448191 / 125000000000000000) (230328134329904301 / 250000000000000000) ((ndm x c)^2) := bsq (lowGroupedE120C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (269671865670095699 / 250000000000000000) (662237695865769873 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE120C_hz41 hx hc) (lowGroupedE120C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE120C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE120C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (269671865670095699 / 500000000000000000) (664489198697295599 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE120C_hz43 hx hc) (lowGroupedE120C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (269671865670095699 / 500000000000000000) (664489198697295599 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE120C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE120C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (170331909671436377 / 250000000000000000) (681327638685749293 / 1000000000000000000) (kdot ((269671865670095699 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (273521011182968589 / 500000000000000000)) (a := (500569374603487069 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (547042022365937177 / 1000000000000000000)) (a := (250284687301740563 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE120C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (146270166707479243 / 200000000000000000) (365675416768698109 / 500000000000000000) (kdot ((664489198697295599 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (112241321459588019 / 250000000000000000)) (a := (84398624775193751 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (17958611433534083 / 40000000000000000)) (a := (26374570242248047 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE120C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (170331909671436377 / 250000000000000000) (365675416768698109 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE120C_hz47 hx hc) (lowGroupedE120C_hz48 hx hc).1 (lowGroupedE120C_hz49 hx hc).2

theorem lowGroupedE120C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE120C_hz51 hx hc) (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE120C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (170331909671436377 / 500000000000000000) (365675416768698109 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE120C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (170331909671436377 / 500000000000000000) (366274895709112199 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE120C_hz54 hx hc) (lowGroupedE120C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (346376562209331757 / 1000000000000000000) (346376562209331987 / 1000000000000000000) ((kdot ((284607923 / 500000000))) / (2 : ℝ)) := bdiv (lowGroupedE120C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (346376562209331757 / 1000000000000000000) (346976041149746077 / 1000000000000000000) (((kdot ((284607923 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE120C_hz56 hx hc) (lowGroupedE120C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE120C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE120C_hz58 hx hc) (lowGroupedE120C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE120C_hz3 hx hc) (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE120C_hz60 hx hc) (lowGroupedE120C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE120C_hz4 hx hc) (lowGroupedE120C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE120C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE120C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (73567205903995081 / 125000000000000000) (589046722382652833 / 1000000000000000000) (√(((kdot ((284607923 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE120C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (73567205903995081 / 125000000000000000) (300113531135075891 / 500000000000000000) ((√(((kdot ((284607923 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE120C_hz65 hx hc) (lowGroupedE120C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (73567205903995081 / 125000000000000000) (300713010075489981 / 500000000000000000) (((√(((kdot ((284607923 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE120C_hz66 hx hc) (lowGroupedE120C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (832317922682590989 / 1000000000000000000) (850544834461590221 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((284607923 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE120C_hz4 hx hc) (lowGroupedE120C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (832317922682590989 / 1000000000000000000) (850544834461590221 / 1000000000000000000) (neb x (kdot (284607923 / 500000000)/2+√23*x)) := by
    convert (lowGroupedE120C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE120C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE120C_hz4 hx hc) (lowGroupedE120C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE120C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE120C_hz3 hx hc) (lowGroupedE120C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE120C_hz71 hx hc) (lowGroupedE120C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE120C_hz4 hx hc) (lowGroupedE120C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE120C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE120C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE120C_hz4 hx hc) (lowGroupedE120C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE120C_hz76 hx hc) (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE120C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE120C_hz4 hx hc) (lowGroupedE120C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE120C_hz79 hx hc) (lowGroupedE120C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE120C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE120C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE120C_hz70 hx hc) (lowGroupedE120C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE120C_hz82 hx hc) (lowGroupedE120C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE120C_hz4 hx hc) (lowGroupedE120C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE120C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE120C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (291832066154009519 / 500000000000000000) (605206490141267569 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE120C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (291832066154009519 / 250000000000000000) (605206490141267569 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE120C_hz70 hx hc) (lowGroupedE120C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (20589543817392921 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE120C_hz87 hx hc) (lowGroupedE120C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE120C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (20878895694613179 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE120C_hz89 hx hc) (lowGroupedE120C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (20878895694613179 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (20878895694613179 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE120C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE120C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE120C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE120C_hz94 hx hc) (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE120C_hz96 hx hc) (lowGroupedE120C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE120C_hz97 hx hc) (lowGroupedE120C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE120C_hz98 hx hc) (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE120C_hz95 hx hc) (lowGroupedE120C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE120C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (541045460539953 / 12500000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE120C_hz93 hx hc) (lowGroupedE120C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (11290142876310161 / 250000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE120C_hz100 hx hc) (lowGroupedE120C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (170331909671436377 / 250000000000000000) (366274895709112199 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE120C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (692753124418663511 / 1000000000000000000) (723426515429293913 / 1000000000000000000) ((neb x (kdot (284607923 / 500000000)/2+√23*x))^2) := bsq (lowGroupedE120C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE120C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE120C_hz106 hx hc) (lowGroupedE120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (692753124418663511 / 1000000000000000000) (723741825441166043 / 1000000000000000000) (((neb x (kdot (284607923 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE120C_hz105 hx hc) (lowGroupedE120C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (117997962613085119 / 250000000000000000) (530176923267571157 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (284607923 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE120C_hz104 hx hc) (lowGroupedE120C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (117997962613085119 / 250000000000000000) (575337494772811801 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (284607923 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE120C_hz103 hx hc) (lowGroupedE120C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE120C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) : B (117997962613085119 / 250000000000000000) (575337494772811801 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (284607923 / 500000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE120C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE120C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (392395949 / 1000000000) (284607923 / 500000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (284607923 / 500000000)/2+√23*x)^2) (np1 x) ≤ (115067499 / 200000000) :=
  (lowGroupedE120C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE140W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE140W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (30686227 / 100000000) (334843829 / 500000000) c := hc

theorem lowGroupedE140W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE140W_hz2 hx hc) (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE140W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE140W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE140W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE140W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE140W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE140W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE140W_hz11 hx hc) (lowGroupedE140W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE140W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE140W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (599279097375252043 / 1000000000000000000) (599279102022139747 / 1000000000000000000) (kdot ((30686227 / 100000000))) := by
    constructor
    · apply bkdot_lower (q := (45517130703972239 / 62500000000000000)) (a := (629450921912889537 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (728274091263555823 / 1000000000000000000)) (a := (629450914613575403 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE140W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (941644527495529 / 10000000000000000) (941644527495529 / 10000000000000000) (((30686227 / 100000000) : ℝ)^2) := bsq (bpoint ((30686227 / 100000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (9058355472504471 / 10000000000000000) (9058355472504471 / 10000000000000000) ((1 : ℝ) - (((30686227 / 100000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE140W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (951753932090877731 / 1000000000000000000) (237938483022719433 / 250000000000000000) (√((1 : ℝ) - (((30686227 / 100000000) : ℝ)^2))) := bsqrt (lowGroupedE140W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (151476342899411263 / 500000000000000000) (302952685798822527 / 1000000000000000000) ((√((1 : ℝ) - (((30686227 / 100000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE140W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (183896144184120883 / 1000000000000000000) (91948072805037697 / 500000000000000000) (((30686227 / 100000000) : ℝ) * (kdot ((30686227 / 100000000)))) := bmul (bpoint ((30686227 / 100000000) : ℝ)) (lowGroupedE140W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (486848829982943409 / 1000000000000000000) (486848831408897921 / 1000000000000000000) (((√((1 : ℝ) - (((30686227 / 100000000) : ℝ)^2))) / Real.pi) + (((30686227 / 100000000) : ℝ) * (kdot ((30686227 / 100000000))))) := badd (lowGroupedE140W_hz18 hx hc) (lowGroupedE140W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (486848829982943409 / 1000000000000000000) (486848831408897921 / 1000000000000000000) (kappa ((30686227 / 100000000))) := by rw [kappa_eq]; exact (lowGroupedE140W_hz20 hx hc)

theorem lowGroupedE140W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (11462062732140827 / 15625000000000000) (73357201485701293 / 100000000000000000) (kdot ((334843829 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (222389760165843011 / 500000000000000000)) (a := (418504100417969381 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (444779520331686021 / 1000000000000000000)) (a := (418504100417969379 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE140W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (112120389819381241 / 250000000000000000) (112120389819381241 / 250000000000000000) (((334843829 / 500000000) : ℝ)^2) := bsq (bpoint ((334843829 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (137879610180618759 / 250000000000000000) (137879610180618759 / 250000000000000000) ((1 : ℝ) - (((334843829 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE140W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (148528575125795243 / 200000000000000000) (92830359453622027 / 125000000000000000) (√((1 : ℝ) - (((334843829 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE140W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (23639056921666243 / 100000000000000000) (236390569216662431 / 1000000000000000000) ((√((1 : ℝ) - (((334843829 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE140W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (30704007787745887 / 62500000000000000) (245632062301967097 / 500000000000000000) (((334843829 / 500000000) : ℝ) * (kdot ((334843829 / 500000000)))) := bmul (bpoint ((334843829 / 500000000) : ℝ)) (lowGroupedE140W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (363827346910298311 / 500000000000000000) (5821237550564773 / 8000000000000000) (((√((1 : ℝ) - (((334843829 / 500000000) : ℝ)^2))) / Real.pi) + (((334843829 / 500000000) : ℝ) * (kdot ((334843829 / 500000000))))) := badd (lowGroupedE140W_hz26 hx hc) (lowGroupedE140W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (363827346910298311 / 500000000000000000) (5821237550564773 / 8000000000000000) (kappa ((334843829 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE140W_hz28 hx hc)

theorem lowGroupedE140W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (486848829982943409 / 1000000000000000000) (5821237550564773 / 8000000000000000) (kappa c) := bkappa (lowGroupedE140W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE140W_hz21 hx hc).1 (lowGroupedE140W_hz29 hx hc).2

theorem lowGroupedE140W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (2178762449435227 / 8000000000000000) (513151170017056591 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE140W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (2178762449435227 / 4000000000000000) (513151170017056591 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE140W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (2178761949435227 / 4000000000000000) (513151170017056591 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE140W_hz32 hx hc) (lowGroupedE140W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (738031494828511197 / 1000000000000000000) (253266453072909113 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE140W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE140W_hz36 hx hc) (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (367320164918474281 / 500000000000000000) (253266453072909113 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE140W_hz35 hx hc) (lowGroupedE140W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (367320164918474281 / 500000000000000000) (253266453072909113 / 250000000000000000) (ndm x c) := by
    convert (lowGroupedE140W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE140W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE140W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE140W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (21587856568917623 / 40000000000000000) (1026302340034113183 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE140W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (973697659965886817 / 1000000000000000000) (1467091665760184699 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE140W_hz41 hx hc) (lowGroupedE140W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE140W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE140W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (30428051873933963 / 62500000000000000) (736039772035314021 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE140W_hz43 hx hc) (lowGroupedE140W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (30428051873933963 / 62500000000000000) (736039772035314021 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE140W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE140W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (330926871907784549 / 500000000000000000) (132370748763138721 / 200000000000000000) (kdot ((30428051873933963 / 62500000000000000))) := by
    constructor
    · apply bkdot_lower (q := (73434352017268747 / 125000000000000000)) (a := (106231779426790031 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (23498992645525999 / 40000000000000000)) (a := (531158897133754581 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE140W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (763306381396903097 / 1000000000000000000) (763306381396903099 / 1000000000000000000) (kdot ((736039772035314021 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (194966240110724127 / 500000000000000000)) (a := (46474683334692103 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (389932480221448253 / 1000000000000000000)) (a := (185898733338768411 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE140W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (330926871907784549 / 500000000000000000) (763306381396903099 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE140W_hz47 hx hc) (lowGroupedE140W_hz48 hx hc).1 (lowGroupedE140W_hz49 hx hc).2

theorem lowGroupedE140W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE140W_hz51 hx hc) (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE140W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (330926871907784549 / 1000000000000000000) (7633063813969031 / 20000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE140W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (330926871907784549 / 1000000000000000000) (9556316740971641 / 25000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE140W_hz54 hx hc) (lowGroupedE140W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (11462062732140827 / 31250000000000000) (73357201485701293 / 200000000000000000) ((kdot ((334843829 / 500000000))) / (2 : ℝ)) := bdiv (lowGroupedE140W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (11462062732140827 / 31250000000000000) (73477097273784111 / 200000000000000000) (((kdot ((334843829 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE140W_hz56 hx hc) (lowGroupedE140W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE140W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE140W_hz58 hx hc) (lowGroupedE140W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE140W_hz3 hx hc) (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE140W_hz60 hx hc) (lowGroupedE140W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE140W_hz4 hx hc) (lowGroupedE140W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE140W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE140W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (605628605193402719 / 1000000000000000000) (75765415754910127 / 125000000000000000) (√(((kdot ((334843829 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE140W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (605628605193402719 / 1000000000000000000) (123460733185355993 / 200000000000000000) ((√(((kdot ((334843829 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE140W_hz65 hx hc) (lowGroupedE140W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (605628605193402719 / 1000000000000000000) (123700524761521629 / 200000000000000000) (((√(((kdot ((334843829 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE140W_hz66 hx hc) (lowGroupedE140W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (856488187225610791 / 1000000000000000000) (174938959790412757 / 200000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((334843829 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE140W_hz4 hx hc) (lowGroupedE140W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (856488187225610791 / 1000000000000000000) (174938959790412757 / 200000000000000000) (neb x (kdot (334843829 / 500000000)/2+√23*x)) := by
    convert (lowGroupedE140W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE140W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE140W_hz4 hx hc) (lowGroupedE140W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE140W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE140W_hz3 hx hc) (lowGroupedE140W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE140W_hz71 hx hc) (lowGroupedE140W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE140W_hz4 hx hc) (lowGroupedE140W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE140W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE140W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE140W_hz4 hx hc) (lowGroupedE140W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE140W_hz76 hx hc) (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE140W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE140W_hz4 hx hc) (lowGroupedE140W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE140W_hz79 hx hc) (lowGroupedE140W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE140W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE140W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE140W_hz70 hx hc) (lowGroupedE140W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE140W_hz82 hx hc) (lowGroupedE140W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE140W_hz4 hx hc) (lowGroupedE140W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE140W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE140W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (575262437421203913 / 1000000000000000000) (123653171352596637 / 200000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE140W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (575262437421203913 / 500000000000000000) (123653171352596637 / 100000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE140W_hz70 hx hc) (lowGroupedE140W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (21033832511690381 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE140W_hz87 hx hc) (lowGroupedE140W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE140W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (21323184388910639 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE140W_hz89 hx hc) (lowGroupedE140W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (21323184388910639 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (21323184388910639 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE140W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE140W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE140W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE140W_hz94 hx hc) (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE140W_hz96 hx hc) (lowGroupedE140W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE140W_hz97 hx hc) (lowGroupedE140W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE140W_hz98 hx hc) (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE140W_hz95 hx hc) (lowGroupedE140W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE140W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (44204683184860307 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE140W_hz93 hx hc) (lowGroupedE140W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (46081617846904711 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE140W_hz100 hx hc) (lowGroupedE140W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (330926871907784549 / 500000000000000000) (9556316740971641 / 12500000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (733572014857012923 / 1000000000000000000) (382545495656895643 / 500000000000000000) ((neb x (kdot (334843829 / 500000000)/2+√23*x))^2) := bsq (lowGroupedE140W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE140W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE140W_hz106 hx hc) (lowGroupedE140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (733572014857012923 / 1000000000000000000) (95675787665707927 / 125000000000000000) (((neb x (kdot (334843829 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE140W_hz105 hx hc) (lowGroupedE140W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (485517384391444279 / 1000000000000000000) (146289301020072433 / 250000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (334843829 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE140W_hz104 hx hc) (lowGroupedE140W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (485517384391444279 / 1000000000000000000) (631238821927194443 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (334843829 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE140W_hz103 hx hc) (lowGroupedE140W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) : B (485517384391444279 / 1000000000000000000) (631238821927194443 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (334843829 / 500000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE140W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE140W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (30686227 / 100000000) (334843829 / 500000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (334843829 / 500000000)/2+√23*x)^2) (np1 x) ≤ (315619411 / 500000000) :=
  (lowGroupedE140W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE140C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE140C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (382501131 / 1000000000) (279629041 / 500000000) c := hc

theorem lowGroupedE140C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE140C_hz2 hx hc) (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE140C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE140C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE140C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE140C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE140C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE140C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE140C_hz11 hx hc) (lowGroupedE140C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE140C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE140C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (624937193147537353 / 1000000000000000000) (624937193216560617 / 1000000000000000000) (kdot ((382501131 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (83540168830697557 / 125000000000000000)) (a := (589147279321232107 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (133664270129116091 / 200000000000000000)) (a := (294573639606405309 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE140C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (146307115216279161 / 1000000000000000000) (146307115216279161 / 1000000000000000000) (((382501131 / 1000000000) : ℝ)^2) := bsq (bpoint ((382501131 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (853692884783720839 / 1000000000000000000) (853692884783720839 / 1000000000000000000) ((1 : ℝ) - (((382501131 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE140C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (923955023138962559 / 1000000000000000000) (1443679723654629 / 1562500000000000) (√((1 : ℝ) - (((382501131 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE140C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (18381501140894053 / 62500000000000000) (294104018254304849 / 1000000000000000000) ((√((1 : ℝ) - (((382501131 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE140C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (239039183182898487 / 1000000000000000000) (59759795802324991 / 250000000000000000) (((382501131 / 1000000000) : ℝ) * (kdot ((382501131 / 1000000000)))) := bmul (bpoint ((382501131 / 1000000000) : ℝ)) (lowGroupedE140C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (106628640287440667 / 200000000000000000) (533143201463604813 / 1000000000000000000) (((√((1 : ℝ) - (((382501131 / 1000000000) : ℝ)^2))) / Real.pi) + (((382501131 / 1000000000) : ℝ) * (kdot ((382501131 / 1000000000))))) := badd (lowGroupedE140C_hz18 hx hc) (lowGroupedE140C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (106628640287440667 / 200000000000000000) (533143201463604813 / 1000000000000000000) (kappa ((382501131 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE140C_hz20 hx hc)

theorem lowGroupedE140C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (688913914920357849 / 1000000000000000000) (344456957460179393 / 500000000000000000) (kdot ((279629041 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (531659008167907781 / 1000000000000000000)) (a := (97730575952021317 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (26582950408395389 / 50000000000000000)) (a := (97730575952021023 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE140C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (78192400570579681 / 250000000000000000) (78192400570579681 / 250000000000000000) (((279629041 / 500000000) : ℝ)^2) := bsq (bpoint ((279629041 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (171807599429420319 / 250000000000000000) (171807599429420319 / 250000000000000000) ((1 : ℝ) - (((279629041 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE140C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (41449680267695711 / 50000000000000000) (828993605353914221 / 1000000000000000000) (√((1 : ℝ) - (((279629041 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE140C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (65969215041823679 / 250000000000000000) (263876860167294717 / 1000000000000000000) ((√((1 : ℝ) - (((279629041 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE140C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (385280674721470513 / 1000000000000000000) (192640337360735519 / 500000000000000000) (((279629041 / 500000000) : ℝ) * (kdot ((279629041 / 500000000)))) := bmul (bpoint ((279629041 / 500000000) : ℝ)) (lowGroupedE140C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (649157534888765229 / 1000000000000000000) (129831506977753151 / 200000000000000000) (((√((1 : ℝ) - (((279629041 / 500000000) : ℝ)^2))) / Real.pi) + (((279629041 / 500000000) : ℝ) * (kdot ((279629041 / 500000000))))) := badd (lowGroupedE140C_hz26 hx hc) (lowGroupedE140C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (649157534888765229 / 1000000000000000000) (129831506977753151 / 200000000000000000) (kappa ((279629041 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE140C_hz28 hx hc)

theorem lowGroupedE140C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (106628640287440667 / 200000000000000000) (129831506977753151 / 200000000000000000) (kappa c) := bkappa (lowGroupedE140C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE140C_hz21 hx hc).1 (lowGroupedE140C_hz29 hx hc).2

theorem lowGroupedE140C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (70168493022246849 / 200000000000000000) (93371359712559333 / 200000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE140C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (70168493022246849 / 100000000000000000) (93371359712559333 / 100000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE140C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (70168480522246849 / 100000000000000000) (93371359712559333 / 100000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE140C_hz32 hx hc) (lowGroupedE140C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (418833142558724837 / 500000000000000000) (966288568247391267 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE140C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE140C_hz36 hx hc) (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (834275120125887039 / 1000000000000000000) (966288568247391267 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE140C_hz35 hx hc) (lowGroupedE140C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (834275120125887039 / 1000000000000000000) (966288568247391267 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE140C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE140C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE140C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE140C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (696014976061063249 / 1000000000000000000) (933713597125593331 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE140C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (1066286402874406669 / 1000000000000000000) (52430924156882481 / 40000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE140C_hz41 hx hc) (lowGroupedE140C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE140C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE140C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (266571600718601667 / 500000000000000000) (164403690498253023 / 250000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE140C_hz43 hx hc) (lowGroupedE140C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (266571600718601667 / 500000000000000000) (164403690498253023 / 250000000000000000) (nc1 x c) := by
    convert (lowGroupedE140C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE140C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (169747326840303277 / 250000000000000000) (84873663420152363 / 125000000000000000) (kdot ((266571600718601667 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (275911935249570941 / 500000000000000000)) (a := (63030302107361501 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (551823870499141881 / 1000000000000000000)) (a := (252121208429441453 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE140C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (145686904100898771 / 200000000000000000) (728434520504493857 / 1000000000000000000) (kdot ((164403690498253023 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (28405061267369493 / 62500000000000000)) (a := (426574057675835867 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (454480980277911887 / 1000000000000000000)) (a := (85314811535167173 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE140C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (169747326840303277 / 250000000000000000) (728434520504493857 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE140C_hz47 hx hc) (lowGroupedE140C_hz48 hx hc).1 (lowGroupedE140C_hz49 hx hc).2

theorem lowGroupedE140C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE140C_hz51 hx hc) (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE140C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (169747326840303277 / 500000000000000000) (364217260252246929 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE140C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (169747326840303277 / 500000000000000000) (364816739192661019 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE140C_hz54 hx hc) (lowGroupedE140C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (86114239365044731 / 250000000000000000) (344456957460179393 / 1000000000000000000) ((kdot ((279629041 / 500000000))) / (2 : ℝ)) := bdiv (lowGroupedE140C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (86114239365044731 / 250000000000000000) (345056436400593483 / 1000000000000000000) (((kdot ((279629041 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE140C_hz56 hx hc) (lowGroupedE140C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE140C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE140C_hz58 hx hc) (lowGroupedE140C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE140C_hz3 hx hc) (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE140C_hz60 hx hc) (lowGroupedE140C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE140C_hz4 hx hc) (lowGroupedE140C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE140C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE140C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (586904555664870371 / 1000000000000000000) (58741504611355801 / 100000000000000000) (√(((kdot ((279629041 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE140C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (586904555664870371 / 1000000000000000000) (598595386001056959 / 1000000000000000000) ((√(((kdot ((279629041 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE140C_hz65 hx hc) (lowGroupedE140C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (586904555664870371 / 1000000000000000000) (599794343881885139 / 1000000000000000000) (((√(((kdot ((279629041 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE140C_hz66 hx hc) (lowGroupedE140C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (830008382439814789 / 1000000000000000000) (84823729575243399 / 100000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((279629041 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE140C_hz4 hx hc) (lowGroupedE140C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (830008382439814789 / 1000000000000000000) (84823729575243399 / 100000000000000000) (neb x (kdot (279629041 / 500000000)/2+√23*x)) := by
    convert (lowGroupedE140C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE140C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE140C_hz4 hx hc) (lowGroupedE140C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE140C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE140C_hz3 hx hc) (lowGroupedE140C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE140C_hz71 hx hc) (lowGroupedE140C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE140C_hz4 hx hc) (lowGroupedE140C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE140C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE140C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE140C_hz4 hx hc) (lowGroupedE140C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE140C_hz76 hx hc) (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE140C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE140C_hz4 hx hc) (lowGroupedE140C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE140C_hz79 hx hc) (lowGroupedE140C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE140C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE140C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE140C_hz70 hx hc) (lowGroupedE140C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE140C_hz82 hx hc) (lowGroupedE140C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE140C_hz4 hx hc) (lowGroupedE140C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE140C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE140C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (582661697454540557 / 1000000000000000000) (15100015297853613 / 25000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE140C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (582661697454540557 / 500000000000000000) (15100015297853613 / 12500000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE140C_hz70 hx hc) (lowGroupedE140C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (10274259502600159 / 500000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE140C_hz87 hx hc) (lowGroupedE140C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE140C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (651183465075643 / 31250000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE140C_hz89 hx hc) (lowGroupedE140C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (651183465075643 / 15625000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (651183465075643 / 15625000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE140C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE140C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE140C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE140C_hz94 hx hc) (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE140C_hz96 hx hc) (lowGroupedE140C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE140C_hz97 hx hc) (lowGroupedE140C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE140C_hz98 hx hc) (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE140C_hz95 hx hc) (lowGroupedE140C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE140C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (43198589094575939 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE140C_hz93 hx hc) (lowGroupedE140C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (45075523756620343 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE140C_hz100 hx hc) (lowGroupedE140C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (169747326840303277 / 250000000000000000) (364816739192661019 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE140C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (344456957460178923 / 500000000000000000) (719506509905402171 / 1000000000000000000) ((neb x (kdot (279629041 / 500000000)/2+√23*x))^2) := bsq (lowGroupedE140C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE140C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE140C_hz106 hx hc) (lowGroupedE140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (344456957460178923 / 500000000000000000) (719821819917274301 / 1000000000000000000) (((neb x (kdot (279629041 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE140C_hz105 hx hc) (lowGroupedE140C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (46776518192327547 / 100000000000000000) (131301524570973433 / 250000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (279629041 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE140C_hz104 hx hc) (lowGroupedE140C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (46776518192327547 / 100000000000000000) (22811264881620563 / 40000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (279629041 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE140C_hz103 hx hc) (lowGroupedE140C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE140C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) : B (46776518192327547 / 100000000000000000) (22811264881620563 / 40000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (279629041 / 500000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE140C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE140C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (382501131 / 1000000000) (279629041 / 500000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (279629041 / 500000000)/2+√23*x)^2) (np1 x) ≤ (570281623 / 1000000000) :=
  (lowGroupedE140C_hz111 hx hc).2.trans (by norm_num)

end BstLean.BlueprintLow
