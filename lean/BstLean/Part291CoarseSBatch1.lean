import BstLean.Part264bNormalize
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
open BstLean.Part264b
theorem lowCoarseS8_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS8_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (19 / 50) (39 / 100) c := hc

theorem lowCoarseS8_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS8_hz2 hx hc) (lowCoarseS8_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS8_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS8_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS8_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS8_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS8_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS8_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS8_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS8_hz10 hx hc) (lowCoarseS8_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS8_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS8_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (312038007376789501 / 500000000000000000) (78009501854155621 / 125000000000000000) (kdot ((19 / 50))) := by
    constructor
    · apply bkdot_lower (q := (670280062599836383 / 1000000000000000000)) (a := (590500015179177013 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (335140031299918191 / 500000000000000000)) (a := (73812501881754751 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS8_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (361 / 2500) (361 / 2500) (((19 / 50) : ℝ)^2) := bsq (bpoint ((19 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (2139 / 2500) (2139 / 2500) ((1 : ℝ) - (((19 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS8_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (924986486387774207 / 1000000000000000000) (3613228462452243 / 3906250000000000) (√((1 : ℝ) - (((19 / 50) : ℝ)^2))) := bsqrt (lowCoarseS8_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (294432343203636847 / 1000000000000000000) (18402021450227303 / 62500000000000000) ((√((1 : ℝ) - (((19 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS8_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (11857444280318001 / 50000000000000000) (463181417259049 / 1953125000000000) (((19 / 50) : ℝ) * (kdot ((19 / 50)))) := bmul (bpoint ((19 / 50) : ℝ)) (lowCoarseS8_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (531581228809996867 / 1000000000000000000) (33223826802516871 / 62500000000000000) (((√((1 : ℝ) - (((19 / 50) : ℝ)^2))) / Real.pi) + (((19 / 50) : ℝ) * (kdot ((19 / 50))))) := badd (lowCoarseS8_hz17 hx hc) (lowCoarseS8_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (531581228809996867 / 1000000000000000000) (33223826802516871 / 62500000000000000) (kappa ((19 / 50))) := by rw [kappa_eq]; exact (lowCoarseS8_hz19 hx hc)

theorem lowCoarseS8_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (627524996667760753 / 1000000000000000000) (627524996712576683 / 1000000000000000000) (kdot ((39 / 100))) := by
    constructor
    · apply bkdot_lower (q := (331228365657030253 / 500000000000000000)) (a := (585082367057198287 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (132491346262812101 / 200000000000000000)) (a := (58508236698680159 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS8_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (1521 / 10000) (1521 / 10000) (((39 / 100) : ℝ)^2) := bsq (bpoint ((39 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (8479 / 10000) (8479 / 10000) ((1 : ℝ) - (((39 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS8_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (460407428263272051 / 500000000000000000) (920814856526544103 / 1000000000000000000) (√((1 : ℝ) - (((39 / 100) : ℝ)^2))) := bsqrt (lowCoarseS8_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (293104472177307789 / 1000000000000000000) (293104472177307791 / 1000000000000000000) ((√((1 : ℝ) - (((39 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS8_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (244734748700426693 / 1000000000000000000) (244734748717904907 / 1000000000000000000) (((39 / 100) : ℝ) * (kdot ((39 / 100)))) := bmul (bpoint ((39 / 100) : ℝ)) (lowCoarseS8_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (268919610438867241 / 500000000000000000) (268919610447606349 / 500000000000000000) (((√((1 : ℝ) - (((39 / 100) : ℝ)^2))) / Real.pi) + (((39 / 100) : ℝ) * (kdot ((39 / 100))))) := badd (lowCoarseS8_hz25 hx hc) (lowCoarseS8_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (268919610438867241 / 500000000000000000) (268919610447606349 / 500000000000000000) (kappa ((39 / 100))) := by rw [kappa_eq]; exact (lowCoarseS8_hz27 hx hc)

theorem lowCoarseS8_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (531581228809996867 / 1000000000000000000) (268919610447606349 / 500000000000000000) (kappa c) := bkappa (lowCoarseS8_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS8_hz20 hx hc).1 (lowCoarseS8_hz28 hx hc).2

theorem lowCoarseS8_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (231080389552393651 / 500000000000000000) (468418771190003133 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS8_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (231080389552393651 / 250000000000000000) (468418771190003133 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS8_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS8_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (231080358302393651 / 250000000000000000) (468418771190003133 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS8_hz31 hx hc) (lowCoarseS8_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (961416368286693257 / 1000000000000000000) (483951842227097599 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS8_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS8_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS8_hz35 hx hc) (lowCoarseS8_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (479012601647565311 / 500000000000000000) (483951842227097599 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS8_hz34 hx hc) (lowCoarseS8_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (479012601647565311 / 500000000000000000) (483951842227097599 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS8_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS8_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS8_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS8_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (917812290148676357 / 1000000000000000000) (234209385595001567 / 250000000000000000) ((ndm x c)^2) := bsq (lowCoarseS8_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (265790614404998433 / 250000000000000000) (1088975789834448917 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS8_hz40 hx hc) (lowCoarseS8_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS8_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS8_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (265790614404998433 / 500000000000000000) (273169533577305551 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS8_hz42 hx hc) (lowCoarseS8_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (265790614404998433 / 500000000000000000) (273169533577305551 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS8_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS8_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (312038007376789501 / 500000000000000000) (627524996712576683 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS8_hz1 hx hc) (lowCoarseS8_hz13 hx hc).1 (lowCoarseS8_hz21 hx hc).2

theorem lowCoarseS8_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (678401969271766549 / 1000000000000000000) (339200984635886499 / 500000000000000000) (kdot ((265790614404998433 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (276514004716781403 / 500000000000000000)) (a := (126291251343095349 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (110605601886712561 / 200000000000000000)) (a := (126291251343092817 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS8_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (341989495481311561 / 500000000000000000) (13679579819252509 / 20000000000000000) (kdot ((273169533577305551 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (541643239208809133 / 1000000000000000000)) (a := (124101160046482107 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (135410809802202283 / 250000000000000000)) (a := (496404640185924773 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS8_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (678401969271766549 / 1000000000000000000) (13679579819252509 / 20000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS8_hz46 hx hc) (lowCoarseS8_hz48 hx hc).1 (lowCoarseS8_hz49 hx hc).2

theorem lowCoarseS8_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (361 / 2500) (1521 / 10000) (c^2) := bsq (lowCoarseS8_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (8479 / 10000) (2139 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS8_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (460407428263272051 / 500000000000000000) (3613228462452243 / 3906250000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS8_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (143664616496743567 / 250000000000000000) (580452141829665867 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS8_hz53 hx hc) (lowCoarseS8_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (143664616496743567 / 250000000000000000) (580452141829665867 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS8_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS8_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (293104472177307789 / 1000000000000000000) (18402021450227303 / 62500000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS8_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (11857444280318001 / 50000000000000000) (244734748717904907 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS8_hz1 hx hc) (lowCoarseS8_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (24184861729701441 / 500000000000000000) (14320864399319207 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS8_hz56 hx hc) (lowCoarseS8_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (24184861729701441 / 500000000000000000) (14320864399319207 / 250000000000000000) (npp c) := by
    convert (lowCoarseS8_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS8_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS8_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS8_hz3 hx hc) (lowCoarseS8_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS8_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS8_hz62 hx hc) (lowCoarseS8_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS8_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS8_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS8_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS8_hz65 hx hc) (lowCoarseS8_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS8_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS8_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS8_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS8_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (143664616496743567 / 250000000000000000) (297424130699802013 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS8_hz55 hx hc) (lowCoarseS8_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (143664616496743567 / 250000000000000000) (595858598118825771 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS8_hz69 hx hc) (lowCoarseS8_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (143664616496743567 / 250000000000000000) (597554180614607089 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS8_hz70 hx hc) (lowCoarseS8_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (143664616496743567 / 250000000000000000) (597554180614607089 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS8_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS8_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS8_hz73 hx hc) (lowCoarseS8_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS8_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS8_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS8_hz3 hx hc) (lowCoarseS8_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS8_hz76 hx hc) (lowCoarseS8_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS8_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS8_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS8_hz80 hx hc) (lowCoarseS8_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS8_hz81 hx hc) (lowCoarseS8_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS8_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS8_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (24184861729701441 / 500000000000000000) (16720217660975567 / 250000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS8_hz59 hx hc) (lowCoarseS8_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (24184861729701441 / 1000000000000000000) (5718138802214769 / 125000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS8_hz84 hx hc) (lowCoarseS8_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (330232352530502461 / 1000000000000000000) (357070998769994471 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS8_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (141289301411573121 / 500000000000000000) (14924318814968533 / 50000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS8_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (35075681185031467 / 50000000000000000) (358710698588426879 / 500000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS8_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (83756410124875179 / 100000000000000000) (847007318254602661 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS8_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (328910653424202049 / 125000000000000000) (2660951968565451693 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS8_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (12410308657639331 / 100000000000000000) (13570212573407949 / 100000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS8_hz86 hx hc) (lowCoarseS8_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (148287948306094751 / 1000000000000000000) (90723618075898821 / 500000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS8_hz85 hx hc) (lowCoarseS8_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS8_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (148287948306094751 / 1000000000000000000) (181450111151797643 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS8_hz92 hx hc) (lowCoarseS8_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (148287948306094751 / 1000000000000000000) (186270867876483857 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS8_hz94 hx hc) (lowCoarseS8_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (148287948306094751 / 1000000000000000000) (186270867876483857 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS8_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS8_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (19386155206388721 / 500000000000000000) (14320864399319207 / 250000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS8_hz59 hx hc) (lowCoarseS8_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS8_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS8_hz50 hx hc) (lowCoarseS8_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS8_hz99 hx hc) (lowCoarseS8_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS8_hz100 hx hc) (lowCoarseS8_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS8_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS8_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (186270867876483857 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS8_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS8_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (186270867876483857 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS8_hz103 hx hc) (lowCoarseS8_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS8_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) : B 0 (186270867876483857 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS8_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS8 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (19 / 50) (39 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS8_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS8_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS8_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS8_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS8_hz38 hx hc).1) (lowCoarseS8_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS8_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS8_hz55 hx hc).1,(lowCoarseS8_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS8_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS8_hz68 hx hc).2 (lowCoarseS8_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS8_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS8_hz55 hx hc).1,(lowCoarseS8_hz64 hx hc).2]

theorem lowCoarseS9_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS9_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (39 / 100) (2 / 5) c := hc

theorem lowCoarseS9_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS9_hz2 hx hc) (lowCoarseS9_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS9_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS9_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS9_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS9_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS9_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS9_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS9_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS9_hz10 hx hc) (lowCoarseS9_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS9_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS9_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (627524996667760753 / 1000000000000000000) (627524996712576683 / 1000000000000000000) (kdot ((39 / 100))) := by
    constructor
    · apply bkdot_lower (q := (331228365657030253 / 500000000000000000)) (a := (585082367057198287 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (132491346262812101 / 200000000000000000)) (a := (58508236698680159 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS9_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (1521 / 10000) (1521 / 10000) (((39 / 100) : ℝ)^2) := bsq (bpoint ((39 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (8479 / 10000) (8479 / 10000) ((1 : ℝ) - (((39 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS9_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (460407428263272051 / 500000000000000000) (920814856526544103 / 1000000000000000000) (√((1 : ℝ) - (((39 / 100) : ℝ)^2))) := bsqrt (lowCoarseS9_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (293104472177307789 / 1000000000000000000) (293104472177307791 / 1000000000000000000) ((√((1 : ℝ) - (((39 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS9_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (244734748700426693 / 1000000000000000000) (244734748717904907 / 1000000000000000000) (((39 / 100) : ℝ) * (kdot ((39 / 100)))) := bmul (bpoint ((39 / 100) : ℝ)) (lowCoarseS9_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (268919610438867241 / 500000000000000000) (268919610447606349 / 500000000000000000) (((√((1 : ℝ) - (((39 / 100) : ℝ)^2))) / Real.pi) + (((39 / 100) : ℝ) * (kdot ((39 / 100))))) := badd (lowCoarseS9_hz17 hx hc) (lowCoarseS9_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (268919610438867241 / 500000000000000000) (268919610447606349 / 500000000000000000) (kappa ((39 / 100))) := by rw [kappa_eq]; exact (lowCoarseS9_hz19 hx hc)

theorem lowCoarseS9_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (315494940215399341 / 500000000000000000) (630989880455876101 / 1000000000000000000) (kdot ((2 / 5))) := by
    constructor
    · apply bkdot_lower (q := (81831708838497143 / 125000000000000000)) (a := (579639740369447029 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (654653670707977143 / 1000000000000000000)) (a := (579639740330055513 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS9_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (4 / 25) (4 / 25) (((2 / 5) : ℝ)^2) := bsq (bpoint ((2 / 5) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (21 / 25) (21 / 25) ((1 : ℝ) - (((2 / 5) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS9_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (916515138991168001 / 1000000000000000000) (458257569495584001 / 500000000000000000) (√((1 : ℝ) - (((2 / 5) : ℝ)^2))) := bsqrt (lowCoarseS9_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (145867914788999887 / 500000000000000000) (11669433183119991 / 40000000000000000) ((√((1 : ℝ) - (((2 / 5) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS9_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (15774747010769967 / 62500000000000000) (252395952182350441 / 1000000000000000000) (((2 / 5) : ℝ) * (kdot ((2 / 5)))) := bmul (bpoint ((2 / 5) : ℝ)) (lowCoarseS9_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (272065890875159623 / 500000000000000000) (68016472720043777 / 125000000000000000) (((√((1 : ℝ) - (((2 / 5) : ℝ)^2))) / Real.pi) + (((2 / 5) : ℝ) * (kdot ((2 / 5))))) := badd (lowCoarseS9_hz25 hx hc) (lowCoarseS9_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (272065890875159623 / 500000000000000000) (68016472720043777 / 125000000000000000) (kappa ((2 / 5))) := by rw [kappa_eq]; exact (lowCoarseS9_hz27 hx hc)

theorem lowCoarseS9_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (268919610438867241 / 500000000000000000) (68016472720043777 / 125000000000000000) (kappa c) := bkappa (lowCoarseS9_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS9_hz20 hx hc).1 (lowCoarseS9_hz28 hx hc).2

theorem lowCoarseS9_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (56983527279956223 / 125000000000000000) (231080389561132759 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS9_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (56983527279956223 / 62500000000000000) (231080389561132759 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS9_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS9_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (56983519467456223 / 62500000000000000) (231080389561132759 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS9_hz31 hx hc) (lowCoarseS9_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (14919513159609159 / 15625000000000000) (60088527082070329 / 62500000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS9_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS9_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS9_hz35 hx hc) (lowCoarseS9_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (951457677223423541 / 1000000000000000000) (60088527082070329 / 62500000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS9_hz34 hx hc) (lowCoarseS9_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (951457677223423541 / 1000000000000000000) (60088527082070329 / 62500000000000000) (ndm x c) := by
    convert (lowCoarseS9_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS9_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS9_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS9_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (181054342309478483 / 200000000000000000) (462160779122265519 / 500000000000000000) ((ndm x c)^2) := bsq (lowCoarseS9_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (537839220877734481 / 500000000000000000) (1101516368435732859 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS9_hz40 hx hc) (lowCoarseS9_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS9_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS9_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (537839220877734481 / 1000000000000000000) (552630674441533549 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS9_hz42 hx hc) (lowCoarseS9_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (537839220877734481 / 1000000000000000000) (552630674441533549 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS9_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS9_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (627524996667760753 / 1000000000000000000) (630989880455876101 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS9_hz1 hx hc) (lowCoarseS9_hz13 hx hc).1 (lowCoarseS9_hz21 hx hc).2

theorem lowCoarseS9_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (170189813947514511 / 250000000000000000) (340379627895031121 / 500000000000000000) (kdot ((537839220877734481 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (548202582224381651 / 1000000000000000000)) (a := (100292437673649197 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (10964051644487633 / 20000000000000000)) (a := (15670693386507481 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS9_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (686375978254993119 / 1000000000000000000) (343187989127497309 / 500000000000000000) (kdot ((552630674441533549 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (134195832564068217 / 250000000000000000)) (a := (492639461351699591 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (536783330256272867 / 1000000000000000000)) (a := (492639461351697239 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS9_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (170189813947514511 / 250000000000000000) (343187989127497309 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS9_hz46 hx hc) (lowCoarseS9_hz48 hx hc).1 (lowCoarseS9_hz49 hx hc).2

theorem lowCoarseS9_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (1521 / 10000) (4 / 25) (c^2) := bsq (lowCoarseS9_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (21 / 25) (8479 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS9_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (916515138991168001 / 1000000000000000000) (920814856526544103 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS9_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (575136159541384983 / 1000000000000000000) (581024856241678767 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS9_hz53 hx hc) (lowCoarseS9_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (575136159541384983 / 1000000000000000000) (581024856241678767 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS9_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS9_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (145867914788999887 / 500000000000000000) (293104472177307791 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS9_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (244734748700426693 / 1000000000000000000) (252395952182350441 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS9_hz1 hx hc) (lowCoarseS9_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (39339877395649333 / 1000000000000000000) (24184861738440549 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS9_hz56 hx hc) (lowCoarseS9_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (39339877395649333 / 1000000000000000000) (24184861738440549 / 500000000000000000) (npp c) := by
    convert (lowCoarseS9_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS9_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS9_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS9_hz3 hx hc) (lowCoarseS9_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS9_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS9_hz62 hx hc) (lowCoarseS9_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS9_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS9_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS9_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS9_hz65 hx hc) (lowCoarseS9_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS9_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS9_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS9_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS9_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (575136159541384983 / 1000000000000000000) (297710487905808463 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS9_hz55 hx hc) (lowCoarseS9_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (575136159541384983 / 1000000000000000000) (596432285273700393 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS9_hz69 hx hc) (lowCoarseS9_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (575136159541384983 / 1000000000000000000) (598127867769481711 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS9_hz70 hx hc) (lowCoarseS9_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (575136159541384983 / 1000000000000000000) (598127867769481711 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS9_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS9_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS9_hz73 hx hc) (lowCoarseS9_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS9_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS9_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS9_hz3 hx hc) (lowCoarseS9_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS9_hz76 hx hc) (lowCoarseS9_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS9_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS9_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS9_hz80 hx hc) (lowCoarseS9_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS9_hz81 hx hc) (lowCoarseS9_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS9_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS9_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (39339877395649333 / 1000000000000000000) (28983568261753269 / 500000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS9_hz59 hx hc) (lowCoarseS9_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (9834969348912333 / 500000000000000000) (9946812509490657 / 250000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS9_hz84 hx hc) (lowCoarseS9_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (516846253143771 / 1562500000000000) (357756946202466599 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS9_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (144635513757184229 / 500000000000000000) (152700331166852121 / 500000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS9_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (347299668833147879 / 500000000000000000) (355364486242815771 / 500000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS9_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (833426264084769383 / 1000000000000000000) (210761857982776313 / 250000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS9_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (1309142914278749219 / 500000000000000000) (2648511618782501537 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS9_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (124893392827202681 / 1000000000000000000) (136637849962915207 / 1000000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS9_hz86 hx hc) (lowCoarseS9_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (144563331525027347 / 1000000000000000000) (35285020000175567 / 200000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS9_hz85 hx hc) (lowCoarseS9_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS9_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (144563331525027347 / 1000000000000000000) (44106993750219459 / 250000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS9_hz92 hx hc) (lowCoarseS9_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (144563331525027347 / 1000000000000000000) (3624974634511281 / 20000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS9_hz94 hx hc) (lowCoarseS9_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (144563331525027347 / 1000000000000000000) (3624974634511281 / 20000000000000000) (nu x c) := by
    convert (lowCoarseS9_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS9_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (29742464349023893 / 1000000000000000000) (24184861738440549 / 500000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS9_hz59 hx hc) (lowCoarseS9_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS9_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS9_hz50 hx hc) (lowCoarseS9_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS9_hz99 hx hc) (lowCoarseS9_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS9_hz100 hx hc) (lowCoarseS9_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS9_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS9_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (3624974634511281 / 20000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS9_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS9_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (3624974634511281 / 20000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS9_hz103 hx hc) (lowCoarseS9_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS9_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) : B 0 (3624974634511281 / 20000000000000000) (ns x c) := by
    convert (lowCoarseS9_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS9 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (39 / 100) (2 / 5) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS9_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS9_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS9_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS9_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS9_hz38 hx hc).1) (lowCoarseS9_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS9_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS9_hz55 hx hc).1,(lowCoarseS9_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS9_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS9_hz68 hx hc).2 (lowCoarseS9_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS9_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS9_hz55 hx hc).1,(lowCoarseS9_hz64 hx hc).2]

theorem lowCoarseS10_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS10_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (2 / 5) (41 / 100) c := hc

theorem lowCoarseS10_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS10_hz2 hx hc) (lowCoarseS10_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS10_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS10_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS10_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS10_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS10_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS10_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS10_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS10_hz10 hx hc) (lowCoarseS10_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS10_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS10_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (315494940215399341 / 500000000000000000) (630989880455876101 / 1000000000000000000) (kdot ((2 / 5))) := by
    constructor
    · apply bkdot_lower (q := (81831708838497143 / 125000000000000000)) (a := (579639740369447029 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (654653670707977143 / 1000000000000000000)) (a := (579639740330055513 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS10_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (4 / 25) (4 / 25) (((2 / 5) : ℝ)^2) := bsq (bpoint ((2 / 5) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (21 / 25) (21 / 25) ((1 : ℝ) - (((2 / 5) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS10_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (916515138991168001 / 1000000000000000000) (458257569495584001 / 500000000000000000) (√((1 : ℝ) - (((2 / 5) : ℝ)^2))) := bsqrt (lowCoarseS10_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (145867914788999887 / 500000000000000000) (11669433183119991 / 40000000000000000) ((√((1 : ℝ) - (((2 / 5) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS10_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (15774747010769967 / 62500000000000000) (252395952182350441 / 1000000000000000000) (((2 / 5) : ℝ) * (kdot ((2 / 5)))) := bmul (bpoint ((2 / 5) : ℝ)) (lowCoarseS10_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (272065890875159623 / 500000000000000000) (68016472720043777 / 125000000000000000) (((√((1 : ℝ) - (((2 / 5) : ℝ)^2))) / Real.pi) + (((2 / 5) : ℝ) * (kdot ((2 / 5))))) := badd (lowCoarseS10_hz17 hx hc) (lowCoarseS10_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (272065890875159623 / 500000000000000000) (68016472720043777 / 125000000000000000) (kappa ((2 / 5))) := by rw [kappa_eq]; exact (lowCoarseS10_hz19 hx hc)

theorem lowCoarseS10_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (12689426089010923 / 20000000000000000) (317235652232250419 / 500000000000000000) (kdot ((41 / 100))) := by
    constructor
    · apply bkdot_lower (q := (646869164755947181 / 1000000000000000000)) (a := (287085566153606091 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (32343458237797359 / 50000000000000000)) (a := (143542783071323053 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS10_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (1681 / 10000) (1681 / 10000) (((41 / 100) : ℝ)^2) := bsq (bpoint ((41 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (8319 / 10000) (8319 / 10000) ((1 : ℝ) - (((41 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS10_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (228021380576471381 / 250000000000000000) (36483420892235421 / 40000000000000000) (√((1 : ℝ) - (((41 / 100) : ℝ)^2))) := bsqrt (lowCoarseS10_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (36290729849383711 / 125000000000000000) (29032583879506969 / 100000000000000000) ((√((1 : ℝ) - (((41 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS10_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (260133234824723921 / 1000000000000000000) (8129163588451417 / 31250000000000000) (((41 / 100) : ℝ) * (kdot ((41 / 100)))) := bmul (bpoint ((41 / 100) : ℝ)) (lowCoarseS10_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (550459073619793609 / 1000000000000000000) (275229536812757517 / 500000000000000000) (((√((1 : ℝ) - (((41 / 100) : ℝ)^2))) / Real.pi) + (((41 / 100) : ℝ) * (kdot ((41 / 100))))) := badd (lowCoarseS10_hz25 hx hc) (lowCoarseS10_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (550459073619793609 / 1000000000000000000) (275229536812757517 / 500000000000000000) (kappa ((41 / 100))) := by rw [kappa_eq]; exact (lowCoarseS10_hz27 hx hc)

theorem lowCoarseS10_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (272065890875159623 / 500000000000000000) (275229536812757517 / 500000000000000000) (kappa c) := bkappa (lowCoarseS10_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS10_hz20 hx hc).1 (lowCoarseS10_hz28 hx hc).2

theorem lowCoarseS10_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (224770463187242483 / 500000000000000000) (227934109124840377 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS10_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (224770463187242483 / 250000000000000000) (227934109124840377 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS10_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS10_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (224770431937242483 / 250000000000000000) (227934109124840377 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS10_hz31 hx hc) (lowCoarseS10_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (474099601283572567 / 500000000000000000) (14919514182513683 / 15625000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS10_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS10_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS10_hz35 hx hc) (lowCoarseS10_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (944808037575582499 / 1000000000000000000) (14919514182513683 / 15625000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS10_hz34 hx hc) (lowCoarseS10_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (944808037575582499 / 1000000000000000000) (14919514182513683 / 15625000000000000) (ndm x c) := by
    convert (lowCoarseS10_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS10_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS10_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS10_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (892662227867423311 / 1000000000000000000) (911736436499361509 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS10_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (1088263563500638491 / 1000000000000000000) (1114125852115701963 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS10_hz40 hx hc) (lowCoarseS10_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS10_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS10_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (108826356350063849 / 200000000000000000) (27947842570047619 / 50000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS10_hz42 hx hc) (lowCoarseS10_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (108826356350063849 / 200000000000000000) (27947842570047619 / 50000000000000000) (nc1 x c) := by
    convert (lowCoarseS10_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS10_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (315494940215399341 / 500000000000000000) (317235652232250419 / 500000000000000000) (kdot c) := bkdot (lowCoarseS10_hz1 hx hc) (lowCoarseS10_hz13 hx hc).1 (lowCoarseS10_hz21 hx hc).2

theorem lowCoarseS10_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (341570423846515779 / 500000000000000000) (341570423846517137 / 500000000000000000) (kdot ((108826356350063849 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (13583681360195751 / 25000000000000000)) (a := (497721192555130721 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (543347254407830039 / 1000000000000000000)) (a := (497721192555126457 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS10_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (172199566284437537 / 250000000000000000) (344399132568875553 / 500000000000000000) (kdot ((27947842570047619 / 50000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (531892041820100763 / 1000000000000000000)) (a := (488834542013821389 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (265946020910050381 / 500000000000000000)) (a := (488834542013819887 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS10_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (341570423846515779 / 500000000000000000) (344399132568875553 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS10_hz46 hx hc) (lowCoarseS10_hz48 hx hc).1 (lowCoarseS10_hz49 hx hc).2

theorem lowCoarseS10_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (4 / 25) (1681 / 10000) (c^2) := bsq (lowCoarseS10_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (8319 / 10000) (21 / 25) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS10_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (228021380576471381 / 250000000000000000) (458257569495584001 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS10_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (57551673466245327 / 100000000000000000) (581502555797189657 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS10_hz53 hx hc) (lowCoarseS10_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (57551673466245327 / 100000000000000000) (581502555797189657 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS10_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS10_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (36290729849383711 / 125000000000000000) (11669433183119991 / 40000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS10_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (15774747010769967 / 62500000000000000) (8129163588451417 / 31250000000000000) (c * (kdot c)) := bmul (lowCoarseS10_hz1 hx hc) (lowCoarseS10_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (3774075495578043 / 125000000000000000) (39339877405680303 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS10_hz56 hx hc) (lowCoarseS10_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (3774075495578043 / 125000000000000000) (39339877405680303 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS10_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS10_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS10_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS10_hz3 hx hc) (lowCoarseS10_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS10_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS10_hz62 hx hc) (lowCoarseS10_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS10_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS10_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS10_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS10_hz65 hx hc) (lowCoarseS10_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS10_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS10_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS10_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS10_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (57551673466245327 / 100000000000000000) (74487334420890977 / 125000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS10_hz55 hx hc) (lowCoarseS10_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (57551673466245327 / 100000000000000000) (596910796191424149 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS10_hz69 hx hc) (lowCoarseS10_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (57551673466245327 / 100000000000000000) (598606378687205467 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS10_hz70 hx hc) (lowCoarseS10_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (57551673466245327 / 100000000000000000) (598606378687205467 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS10_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS10_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS10_hz73 hx hc) (lowCoarseS10_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS10_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS10_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS10_hz3 hx hc) (lowCoarseS10_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS10_hz76 hx hc) (lowCoarseS10_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS10_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS10_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS10_hz80 hx hc) (lowCoarseS10_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS10_hz81 hx hc) (lowCoarseS10_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS10_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS10_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (3774075495578043 / 125000000000000000) (48937290452305743 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS10_hz59 hx hc) (lowCoarseS10_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (3774075495578043 / 250000000000000000) (33707920764090427 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS10_hz84 hx hc) (lowCoarseS10_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (331219511876532641 / 1000000000000000000) (89582399151252509 / 250000000000000000) ((nlam x c)^2) := bsq (lowCoarseS10_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (59215879182155411 / 200000000000000000) (312432761728066361 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS10_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (687567238271933639 / 1000000000000000000) (140784120817844589 / 200000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS10_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (207299185700271993 / 250000000000000000) (838999764057906601 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS10_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (520999679112896649 / 200000000000000000) (2635795495127889233 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS10_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (31415516917831083 / 250000000000000000) (137554632361822531 / 1000000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS10_hz86 hx hc) (lowCoarseS10_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (17594796206704563 / 125000000000000000) (85631276562956479 / 500000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS10_hz85 hx hc) (lowCoarseS10_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS10_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (17594796206704563 / 125000000000000000) (171265428125912959 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS10_hz92 hx hc) (lowCoarseS10_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (17594796206704563 / 125000000000000000) (176086184850599173 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS10_hz94 hx hc) (lowCoarseS10_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (17594796206704563 / 125000000000000000) (176086184850599173 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS10_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS10_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (2574398864749863 / 125000000000000000) (39339877405680303 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS10_hz59 hx hc) (lowCoarseS10_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS10_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS10_hz50 hx hc) (lowCoarseS10_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS10_hz99 hx hc) (lowCoarseS10_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS10_hz100 hx hc) (lowCoarseS10_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS10_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS10_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (176086184850599173 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS10_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS10_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (176086184850599173 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS10_hz103 hx hc) (lowCoarseS10_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS10_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) : B 0 (176086184850599173 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS10_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS10 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (2 / 5) (41 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS10_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS10_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS10_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS10_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS10_hz38 hx hc).1) (lowCoarseS10_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS10_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS10_hz55 hx hc).1,(lowCoarseS10_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS10_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS10_hz68 hx hc).2 (lowCoarseS10_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS10_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS10_hz55 hx hc).1,(lowCoarseS10_hz64 hx hc).2]

theorem lowCoarseS11_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS11_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (41 / 100) (21 / 50) c := hc

theorem lowCoarseS11_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS11_hz2 hx hc) (lowCoarseS11_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS11_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS11_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS11_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS11_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS11_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS11_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS11_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS11_hz10 hx hc) (lowCoarseS11_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS11_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS11_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (12689426089010923 / 20000000000000000) (317235652232250419 / 500000000000000000) (kdot ((41 / 100))) := by
    constructor
    · apply bkdot_lower (q := (646869164755947181 / 1000000000000000000)) (a := (287085566153606091 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (32343458237797359 / 50000000000000000)) (a := (143542783071323053 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS11_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (1681 / 10000) (1681 / 10000) (((41 / 100) : ℝ)^2) := bsq (bpoint ((41 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (8319 / 10000) (8319 / 10000) ((1 : ℝ) - (((41 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS11_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (228021380576471381 / 250000000000000000) (36483420892235421 / 40000000000000000) (√((1 : ℝ) - (((41 / 100) : ℝ)^2))) := bsqrt (lowCoarseS11_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (36290729849383711 / 125000000000000000) (29032583879506969 / 100000000000000000) ((√((1 : ℝ) - (((41 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS11_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (260133234824723921 / 1000000000000000000) (8129163588451417 / 31250000000000000) (((41 / 100) : ℝ) * (kdot ((41 / 100)))) := bmul (bpoint ((41 / 100) : ℝ)) (lowCoarseS11_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (550459073619793609 / 1000000000000000000) (275229536812757517 / 500000000000000000) (((√((1 : ℝ) - (((41 / 100) : ℝ)^2))) / Real.pi) + (((41 / 100) : ℝ) * (kdot ((41 / 100))))) := badd (lowCoarseS11_hz17 hx hc) (lowCoarseS11_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (550459073619793609 / 1000000000000000000) (275229536812757517 / 500000000000000000) (kappa ((41 / 100))) := by rw [kappa_eq]; exact (lowCoarseS11_hz19 hx hc)

theorem lowCoarseS11_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (12759398609945091 / 20000000000000000) (318984965252487437 / 500000000000000000) (kdot ((21 / 50))) := by
    constructor
    · apply bkdot_lower (q := (127820296389165381 / 200000000000000000)) (a := (284337751682106839 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (79887685243228363 / 125000000000000000)) (a := (284337751676043311 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS11_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (441 / 2500) (441 / 2500) (((21 / 50) : ℝ)^2) := bsq (bpoint ((21 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (2059 / 2500) (2059 / 2500) ((1 : ℝ) - (((21 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS11_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (226881026090768551 / 250000000000000000) (181504820872614841 / 200000000000000000) (√((1 : ℝ) - (((21 / 50) : ℝ)^2))) := bsqrt (lowCoarseS11_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (288873894368856717 / 1000000000000000000) (144436947184428359 / 500000000000000000) ((√((1 : ℝ) - (((21 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS11_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (267947370808846911 / 1000000000000000000) (33493421351511181 / 125000000000000000) (((21 / 50) : ℝ) * (kdot ((21 / 50)))) := bmul (bpoint ((21 / 50) : ℝ)) (lowCoarseS11_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (139205316294425907 / 250000000000000000) (278410632590473083 / 500000000000000000) (((√((1 : ℝ) - (((21 / 50) : ℝ)^2))) / Real.pi) + (((21 / 50) : ℝ) * (kdot ((21 / 50))))) := badd (lowCoarseS11_hz25 hx hc) (lowCoarseS11_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (139205316294425907 / 250000000000000000) (278410632590473083 / 500000000000000000) (kappa ((21 / 50))) := by rw [kappa_eq]; exact (lowCoarseS11_hz27 hx hc)

theorem lowCoarseS11_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (550459073619793609 / 1000000000000000000) (278410632590473083 / 500000000000000000) (kappa c) := bkappa (lowCoarseS11_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS11_hz20 hx hc).1 (lowCoarseS11_hz28 hx hc).2

theorem lowCoarseS11_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (221589367409526917 / 500000000000000000) (449540926380206391 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS11_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (221589367409526917 / 250000000000000000) (449540926380206391 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS11_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS11_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (221589336159526917 / 250000000000000000) (449540926380206391 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS11_hz31 hx hc) (lowCoarseS11_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (235366382561065269 / 250000000000000000) (474099634243798163 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS11_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS11_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS11_hz35 hx hc) (lowCoarseS11_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (938074365252698441 / 1000000000000000000) (474099634243798163 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS11_hz34 hx hc) (lowCoarseS11_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (938074365252698441 / 1000000000000000000) (474099634243798163 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS11_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS11_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS11_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS11_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (219995878686063271 / 250000000000000000) (56192615797525799 / 62500000000000000) ((ndm x c)^2) := bsq (lowCoarseS11_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (68807384202474201 / 62500000000000000) (112680456523887219 / 100000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS11_hz40 hx hc) (lowCoarseS11_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS11_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS11_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (68807384202474201 / 125000000000000000) (565317760766519453 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS11_hz42 hx hc) (lowCoarseS11_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (68807384202474201 / 125000000000000000) (565317760766519453 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS11_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS11_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (12689426089010923 / 20000000000000000) (318984965252487437 / 500000000000000000) (kdot c) := bkdot (lowCoarseS11_hz1 hx hc) (lowCoarseS11_hz13 hx hc).1 (lowCoarseS11_hz21 hx hc).2

theorem lowCoarseS11_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (342773647329963201 / 500000000000000000) (685547294659928147 / 1000000000000000000) (kdot ((68807384202474201 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (134615315467896513 / 250000000000000000)) (a := (24697057724945279 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (538461261871586051 / 1000000000000000000)) (a := (12348528862472571 / 25000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS11_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (691246444961434089 / 1000000000000000000) (86405805620179337 / 125000000000000000) (kdot ((565317760766519453 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (105393708657736209 / 200000000000000000)) (a := (242494475069722639 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (131742135822170261 / 250000000000000000)) (a := (19399558005577773 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS11_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (342773647329963201 / 500000000000000000) (86405805620179337 / 125000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS11_hz46 hx hc) (lowCoarseS11_hz48 hx hc).1 (lowCoarseS11_hz49 hx hc).2

theorem lowCoarseS11_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (1681 / 10000) (441 / 2500) (c^2) := bsq (lowCoarseS11_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (2059 / 2500) (8319 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS11_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (226881026090768551 / 250000000000000000) (36483420892235421 / 40000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS11_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (57579800231555327 / 100000000000000000) (581883137280079499 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS11_hz53 hx hc) (lowCoarseS11_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (57579800231555327 / 100000000000000000) (581883137280079499 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS11_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS11_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (288873894368856717 / 1000000000000000000) (29032583879506969 / 100000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS11_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (260133234824723921 / 1000000000000000000) (33493421351511181 / 125000000000000000) (c * (kdot c)) := bmul (lowCoarseS11_hz1 hx hc) (lowCoarseS11_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (20926523556767269 / 1000000000000000000) (30192603970345769 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS11_hz56 hx hc) (lowCoarseS11_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (20926523556767269 / 1000000000000000000) (30192603970345769 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS11_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS11_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS11_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS11_hz3 hx hc) (lowCoarseS11_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS11_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS11_hz62 hx hc) (lowCoarseS11_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS11_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS11_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS11_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS11_hz65 hx hc) (lowCoarseS11_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS11_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS11_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS11_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS11_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (57579800231555327 / 100000000000000000) (298139628425008829 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS11_hz55 hx hc) (lowCoarseS11_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (57579800231555327 / 100000000000000000) (597292024083611573 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS11_hz69 hx hc) (lowCoarseS11_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (57579800231555327 / 100000000000000000) (598987606579392891 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS11_hz70 hx hc) (lowCoarseS11_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (57579800231555327 / 100000000000000000) (598987606579392891 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS11_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS11_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS11_hz73 hx hc) (lowCoarseS11_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS11_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS11_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS11_hz3 hx hc) (lowCoarseS11_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS11_hz76 hx hc) (lowCoarseS11_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS11_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS11_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS11_hz80 hx hc) (lowCoarseS11_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS11_hz81 hx hc) (lowCoarseS11_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS11_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS11_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (20926523556767269 / 1000000000000000000) (39790017016971209 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS11_hz59 hx hc) (lowCoarseS11_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (5231630889191817 / 500000000000000000) (27504707807936339 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS11_hz84 hx hc) (lowCoarseS11_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (2590182339613921 / 7812500000000000) (179393076417854779 / 500000000000000000) ((nlam x c)^2) := bsq (lowCoarseS11_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (303005191730361359 / 1000000000000000000) (319584170638071721 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS11_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (680415829361928279 / 1000000000000000000) (696994808269638641 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS11_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (164974644035006577 / 200000000000000000) (208715537315391101 / 250000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS11_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (2591415648644839333 / 1000000000000000000) (1311398397440158079 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS11_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (15801040139563639 / 125000000000000000) (69225898404861063 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS11_hz86 hx hc) (lowCoarseS11_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (68435791447446373 / 500000000000000000) (33191300923531693 / 200000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS11_hz85 hx hc) (lowCoarseS11_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS11_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (68435791447446373 / 500000000000000000) (82979689808829233 / 500000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS11_hz92 hx hc) (lowCoarseS11_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (68435791447446373 / 500000000000000000) (4269503408558617 / 25000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS11_hz94 hx hc) (lowCoarseS11_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (68435791447446373 / 500000000000000000) (4269503408558617 / 25000000000000000) (nu x c) := by
    convert (lowCoarseS11_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS11_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (11329110510141829 / 1000000000000000000) (30192603970345769 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS11_hz59 hx hc) (lowCoarseS11_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS11_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS11_hz50 hx hc) (lowCoarseS11_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS11_hz99 hx hc) (lowCoarseS11_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS11_hz100 hx hc) (lowCoarseS11_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS11_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS11_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (4269503408558617 / 25000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS11_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS11_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (4269503408558617 / 25000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS11_hz103 hx hc) (lowCoarseS11_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS11_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) : B 0 (4269503408558617 / 25000000000000000) (ns x c) := by
    convert (lowCoarseS11_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS11 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (41 / 100) (21 / 50) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS11_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS11_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS11_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS11_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS11_hz38 hx hc).1) (lowCoarseS11_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS11_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS11_hz55 hx hc).1,(lowCoarseS11_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS11_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS11_hz68 hx hc).2 (lowCoarseS11_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS11_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS11_hz55 hx hc).1,(lowCoarseS11_hz64 hx hc).2]

theorem lowCoarseS12_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS12_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (21 / 50) (43 / 100) c := hc

theorem lowCoarseS12_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS12_hz2 hx hc) (lowCoarseS12_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS12_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS12_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS12_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS12_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS12_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS12_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS12_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS12_hz10 hx hc) (lowCoarseS12_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS12_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS12_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (12759398609945091 / 20000000000000000) (318984965252487437 / 500000000000000000) (kdot ((21 / 50))) := by
    constructor
    · apply bkdot_lower (q := (127820296389165381 / 200000000000000000)) (a := (284337751682106839 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (79887685243228363 / 125000000000000000)) (a := (284337751676043311 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS12_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (441 / 2500) (441 / 2500) (((21 / 50) : ℝ)^2) := bsq (bpoint ((21 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (2059 / 2500) (2059 / 2500) ((1 : ℝ) - (((21 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS12_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (226881026090768551 / 250000000000000000) (181504820872614841 / 200000000000000000) (√((1 : ℝ) - (((21 / 50) : ℝ)^2))) := bsqrt (lowCoarseS12_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (288873894368856717 / 1000000000000000000) (144436947184428359 / 500000000000000000) ((√((1 : ℝ) - (((21 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS12_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (267947370808846911 / 1000000000000000000) (33493421351511181 / 125000000000000000) (((21 / 50) : ℝ) * (kdot ((21 / 50)))) := bmul (bpoint ((21 / 50) : ℝ)) (lowCoarseS12_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (139205316294425907 / 250000000000000000) (278410632590473083 / 500000000000000000) (((√((1 : ℝ) - (((21 / 50) : ℝ)^2))) / Real.pi) + (((21 / 50) : ℝ) * (kdot ((21 / 50))))) := badd (lowCoarseS12_hz17 hx hc) (lowCoarseS12_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (139205316294425907 / 250000000000000000) (278410632590473083 / 500000000000000000) (kappa ((21 / 50))) := by rw [kappa_eq]; exact (lowCoarseS12_hz19 hx hc)

theorem lowCoarseS12_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (160371611308842497 / 250000000000000000) (128297289047923071 / 200000000000000000) (kdot ((43 / 100))) := by
    constructor
    · apply bkdot_lower (q := (631348872337156077 / 1000000000000000000)) (a := (56315177493046183 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (157837218084289019 / 250000000000000000)) (a := (70393971865474153 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS12_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (1849 / 10000) (1849 / 10000) (((43 / 100) : ℝ)^2) := bsq (bpoint ((43 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (8151 / 10000) (8151 / 10000) ((1 : ℝ) - (((43 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS12_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (902828887442133189 / 1000000000000000000) (90282888744213319 / 100000000000000000) (√((1 : ℝ) - (((43 / 100) : ℝ)^2))) := bsqrt (lowCoarseS12_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (143689680202571887 / 500000000000000000) (11495174416205751 / 40000000000000000) ((√((1 : ℝ) - (((43 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS12_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (137919585725604547 / 500000000000000000) (275839171453034603 / 1000000000000000000) (((43 / 100) : ℝ) * (kdot ((43 / 100)))) := bmul (bpoint ((43 / 100) : ℝ)) (lowCoarseS12_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (140804632964088217 / 250000000000000000) (281609265929089189 / 500000000000000000) (((√((1 : ℝ) - (((43 / 100) : ℝ)^2))) / Real.pi) + (((43 / 100) : ℝ) * (kdot ((43 / 100))))) := badd (lowCoarseS12_hz25 hx hc) (lowCoarseS12_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (140804632964088217 / 250000000000000000) (281609265929089189 / 500000000000000000) (kappa ((43 / 100))) := by rw [kappa_eq]; exact (lowCoarseS12_hz27 hx hc)

theorem lowCoarseS12_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (139205316294425907 / 250000000000000000) (281609265929089189 / 500000000000000000) (kappa c) := bkappa (lowCoarseS12_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS12_hz20 hx hc).1 (lowCoarseS12_hz28 hx hc).2

theorem lowCoarseS12_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (218390734070910811 / 500000000000000000) (110794683705574093 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS12_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (218390734070910811 / 250000000000000000) (110794683705574093 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS12_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS12_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (218390702820910811 / 250000000000000000) (110794683705574093 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS12_hz31 hx hc) (lowCoarseS12_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (934645821305398681 / 1000000000000000000) (941465596633564059 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS12_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS12_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS12_hz35 hx hc) (lowCoarseS12_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (465627328156918023 / 500000000000000000) (941465596633564059 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS12_hz34 hx hc) (lowCoarseS12_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (465627328156918023 / 500000000000000000) (941465596633564059 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS12_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS12_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS12_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS12_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (433617617453100447 / 500000000000000000) (443178734822296373 / 500000000000000000) ((ndm x c)^2) := bsq (lowCoarseS12_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (556821265177703627 / 500000000000000000) (56977642253846219 / 50000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS12_hz40 hx hc) (lowCoarseS12_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS12_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS12_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (556821265177703627 / 1000000000000000000) (285856785873705113 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS12_hz42 hx hc) (lowCoarseS12_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (556821265177703627 / 1000000000000000000) (285856785873705113 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS12_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS12_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (12759398609945091 / 20000000000000000) (128297289047923071 / 200000000000000000) (kdot c) := bkdot (lowCoarseS12_hz1 hx hc) (lowCoarseS12_hz13 hx hc).1 (lowCoarseS12_hz21 hx hc).2

theorem lowCoarseS12_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (343989585681801509 / 500000000000000000) (687979171363604131 / 1000000000000000000) (kdot ((556821265177703627 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (106708760370055899 / 200000000000000000)) (a := (490121171505552271 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (266771900925139747 / 500000000000000000)) (a := (490121171505550523 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS12_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (86715142339271821 / 125000000000000000) (693721138714174951 / 1000000000000000000) (kdot ((285856785873705113 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (130502990358167853 / 250000000000000000)) (a := (96220342056539651 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (522011961432671411 / 1000000000000000000)) (a := (96220342056539531 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS12_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (343989585681801509 / 500000000000000000) (693721138714174951 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS12_hz46 hx hc) (lowCoarseS12_hz48 hx hc).1 (lowCoarseS12_hz49 hx hc).2

theorem lowCoarseS12_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (441 / 2500) (1849 / 10000) (c^2) := bsq (lowCoarseS12_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (8151 / 10000) (2059 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS12_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (902828887442133189 / 1000000000000000000) (181504820872614841 / 200000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS12_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (575977682572371361 / 1000000000000000000) (145541102919283543 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS12_hz53 hx hc) (lowCoarseS12_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (575977682572371361 / 1000000000000000000) (145541102919283543 / 250000000000000000) (npa c) := by
    convert (lowCoarseS12_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS12_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (143689680202571887 / 500000000000000000) (144436947184428359 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS12_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (267947370808846911 / 1000000000000000000) (275839171453034603 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS12_hz1 hx hc) (lowCoarseS12_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (11540188952109171 / 1000000000000000000) (20926523560009807 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS12_hz56 hx hc) (lowCoarseS12_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (11540188952109171 / 1000000000000000000) (20926523560009807 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS12_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS12_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS12_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS12_hz3 hx hc) (lowCoarseS12_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS12_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS12_hz62 hx hc) (lowCoarseS12_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS12_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS12_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS12_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS12_hz65 hx hc) (lowCoarseS12_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS12_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS12_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS12_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS12_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (575977682572371361 / 1000000000000000000) (596560531247072331 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS12_hz55 hx hc) (lowCoarseS12_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (575977682572371361 / 1000000000000000000) (119514755243811527 / 200000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS12_hz69 hx hc) (lowCoarseS12_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (575977682572371361 / 1000000000000000000) (599269358714838953 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS12_hz70 hx hc) (lowCoarseS12_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (575977682572371361 / 1000000000000000000) (599269358714838953 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS12_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS12_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS12_hz73 hx hc) (lowCoarseS12_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS12_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS12_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS12_hz3 hx hc) (lowCoarseS12_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS12_hz76 hx hc) (lowCoarseS12_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS12_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS12_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS12_hz80 hx hc) (lowCoarseS12_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS12_hz81 hx hc) (lowCoarseS12_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS12_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS12_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (11540188952109171 / 1000000000000000000) (30523936606635247 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS12_hz59 hx hc) (lowCoarseS12_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (1154018895210917 / 200000000000000000) (21175100060794293 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS12_hz84 hx hc) (lowCoarseS12_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (331750290821439383 / 1000000000000000000) (179561882147247163 / 500000000000000000) ((nlam x c)^2) := bsq (lowCoarseS12_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (310049921354098541 / 1000000000000000000) (326856408120181181 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS12_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (673143591879818819 / 1000000000000000000) (689950078645901459 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS12_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (820453284398215337 / 1000000000000000000) (830632336624274133 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS12_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (644382502719762657 / 250000000000000000) (1304754223286471887 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS12_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (12713133435422507 / 100000000000000000) (69664322583778063 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS12_hz86 hx hc) (lowCoarseS12_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (26580285766055931 / 200000000000000000) (160503745228350419 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS12_hz85 hx hc) (lowCoarseS12_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS12_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (26580285766055931 / 200000000000000000) (8025331011417521 / 50000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS12_hz92 hx hc) (lowCoarseS12_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (26580285766055931 / 200000000000000000) (82663688476518317 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS12_hz94 hx hc) (lowCoarseS12_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (26580285766055931 / 200000000000000000) (82663688476518317 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS12_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS12_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (1942775905483731 / 1000000000000000000) (20926523560009807 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS12_hz59 hx hc) (lowCoarseS12_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS12_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS12_hz50 hx hc) (lowCoarseS12_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS12_hz99 hx hc) (lowCoarseS12_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS12_hz100 hx hc) (lowCoarseS12_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS12_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS12_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (82663688476518317 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS12_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS12_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (82663688476518317 / 500000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS12_hz103 hx hc) (lowCoarseS12_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS12_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) : B 0 (82663688476518317 / 500000000000000000) (ns x c) := by
    convert (lowCoarseS12_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS12 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (21 / 50) (43 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS12_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS12_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS12_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS12_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS12_hz38 hx hc).1) (lowCoarseS12_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS12_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS12_hz55 hx hc).1,(lowCoarseS12_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS12_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS12_hz68 hx hc).2 (lowCoarseS12_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS12_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS12_hz55 hx hc).1,(lowCoarseS12_hz64 hx hc).2]

theorem lowCoarseS13_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS13_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (43 / 100) (11 / 25) c := hc

theorem lowCoarseS13_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS13_hz2 hx hc) (lowCoarseS13_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS13_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS13_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS13_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS13_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS13_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS13_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS13_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS13_hz10 hx hc) (lowCoarseS13_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS13_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS13_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (160371611308842497 / 250000000000000000) (128297289047923071 / 200000000000000000) (kdot ((43 / 100))) := by
    constructor
    · apply bkdot_lower (q := (631348872337156077 / 1000000000000000000)) (a := (56315177493046183 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (157837218084289019 / 250000000000000000)) (a := (70393971865474153 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS13_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (1849 / 10000) (1849 / 10000) (((43 / 100) : ℝ)^2) := bsq (bpoint ((43 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (8151 / 10000) (8151 / 10000) ((1 : ℝ) - (((43 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS13_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (902828887442133189 / 1000000000000000000) (90282888744213319 / 100000000000000000) (√((1 : ℝ) - (((43 / 100) : ℝ)^2))) := bsqrt (lowCoarseS13_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (143689680202571887 / 500000000000000000) (11495174416205751 / 40000000000000000) ((√((1 : ℝ) - (((43 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS13_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (137919585725604547 / 500000000000000000) (275839171453034603 / 1000000000000000000) (((43 / 100) : ℝ) * (kdot ((43 / 100)))) := bmul (bpoint ((43 / 100) : ℝ)) (lowCoarseS13_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (140804632964088217 / 250000000000000000) (281609265929089189 / 500000000000000000) (((√((1 : ℝ) - (((43 / 100) : ℝ)^2))) / Real.pi) + (((43 / 100) : ℝ) * (kdot ((43 / 100))))) := badd (lowCoarseS13_hz17 hx hc) (lowCoarseS13_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (140804632964088217 / 250000000000000000) (281609265929089189 / 500000000000000000) (kappa ((43 / 100))) := by rw [kappa_eq]; exact (lowCoarseS13_hz19 hx hc)

theorem lowCoarseS13_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (322510780936897579 / 500000000000000000) (645021561876114903 / 1000000000000000000) (kdot ((11 / 25))) := by
    constructor
    · apply bkdot_lower (q := (124721912892464713 / 200000000000000000)) (a := (557598826700032049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (155902391115580891 / 250000000000000000)) (a := (111519765339277641 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS13_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (121 / 625) (121 / 625) (((11 / 25) : ℝ)^2) := bsq (bpoint ((11 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (504 / 625) (504 / 625) ((1 : ℝ) - (((11 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS13_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (224499443206436483 / 250000000000000000) (897997772825745933 / 1000000000000000000) (√((1 : ℝ) - (((11 / 25) : ℝ)^2))) := bsqrt (lowCoarseS13_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (285841568861460699 / 1000000000000000000) (2858415688614607 / 10000000000000000) ((√((1 : ℝ) - (((11 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS13_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (283809487224469869 / 1000000000000000000) (141904743612745279 / 500000000000000000) (((11 / 25) : ℝ) * (kdot ((11 / 25)))) := bmul (bpoint ((11 / 25) : ℝ)) (lowCoarseS13_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (71206382010741321 / 125000000000000000) (284825528043475629 / 500000000000000000) (((√((1 : ℝ) - (((11 / 25) : ℝ)^2))) / Real.pi) + (((11 / 25) : ℝ) * (kdot ((11 / 25))))) := badd (lowCoarseS13_hz25 hx hc) (lowCoarseS13_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (71206382010741321 / 125000000000000000) (284825528043475629 / 500000000000000000) (kappa ((11 / 25))) := by rw [kappa_eq]; exact (lowCoarseS13_hz27 hx hc)

theorem lowCoarseS13_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (140804632964088217 / 250000000000000000) (284825528043475629 / 500000000000000000) (kappa c) := bkappa (lowCoarseS13_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS13_hz20 hx hc).1 (lowCoarseS13_hz28 hx hc).2

theorem lowCoarseS13_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (215174471956524371 / 500000000000000000) (109195367035911783 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS13_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (215174471956524371 / 250000000000000000) (109195367035911783 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS13_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS13_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (215174440706524371 / 250000000000000000) (109195367035911783 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS13_hz31 hx hc) (lowCoarseS13_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (92773798177400147 / 100000000000000000) (934645888177599733 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS13_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS13_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS13_hz35 hx hc) (lowCoarseS13_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (184869363356487767 / 200000000000000000) (934645888177599733 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS13_hz34 hx hc) (lowCoarseS13_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (184869363356487767 / 200000000000000000) (934645888177599733 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS13_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS13_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS13_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS13_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (213604259423956887 / 250000000000000000) (174712587257458853 / 200000000000000000) ((ndm x c)^2) := bsq (lowCoarseS13_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (225287412742541147 / 200000000000000000) (576185521143648863 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS13_hz40 hx hc) (lowCoarseS13_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS13_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS13_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (563218531856352867 / 1000000000000000000) (144536115067108513 / 250000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS13_hz42 hx hc) (lowCoarseS13_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (563218531856352867 / 1000000000000000000) (144536115067108513 / 250000000000000000) (nc1 x c) := by
    convert (lowCoarseS13_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS13_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (160371611308842497 / 250000000000000000) (645021561876114903 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS13_hz1 hx hc) (lowCoarseS13_hz13 hx hc).1 (lowCoarseS13_hz21 hx hc).2

theorem lowCoarseS13_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (138087415794231231 / 200000000000000000) (345218539485578431 / 500000000000000000) (kdot ((563218531856352867 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (33037126917023821 / 62500000000000000)) (a := (48626029926400657 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (105718806134476227 / 200000000000000000)) (a := (243130149632002731 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS13_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (696222996734047743 / 1000000000000000000) (696222996734047983 / 1000000000000000000) (kdot ((144536115067108513 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (258510688914179931 / 500000000000000000)) (a := (238585900447459559 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (517021377828359861 / 1000000000000000000)) (a := (477171800894918743 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS13_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (138087415794231231 / 200000000000000000) (696222996734047983 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS13_hz46 hx hc) (lowCoarseS13_hz48 hx hc).1 (lowCoarseS13_hz49 hx hc).2

theorem lowCoarseS13_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (1849 / 10000) (121 / 625) (c^2) := bsq (lowCoarseS13_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (504 / 625) (8151 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS13_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (224499443206436483 / 250000000000000000) (90282888744213319 / 100000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS13_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (576053399119267087 / 1000000000000000000) (582344099084799891 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS13_hz53 hx hc) (lowCoarseS13_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (576053399119267087 / 1000000000000000000) (582344099084799891 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS13_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS13_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (285841568861460699 / 1000000000000000000) (11495174416205751 / 40000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS13_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (137919585725604547 / 500000000000000000) (141904743612745279 / 500000000000000000) (c * (kdot c)) := bmul (lowCoarseS13_hz1 hx hc) (lowCoarseS13_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (2032081635970141 / 1000000000000000000) (11540188953934681 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS13_hz56 hx hc) (lowCoarseS13_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (2032081635970141 / 1000000000000000000) (11540188953934681 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS13_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS13_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS13_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS13_hz3 hx hc) (lowCoarseS13_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS13_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS13_hz62 hx hc) (lowCoarseS13_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS13_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS13_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS13_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS13_hz65 hx hc) (lowCoarseS13_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS13_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS13_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS13_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS13_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (576053399119267087 / 1000000000000000000) (11934804373094761 / 20000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS13_hz55 hx hc) (lowCoarseS13_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (576053399119267087 / 1000000000000000000) (59775376882184239 / 100000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS13_hz69 hx hc) (lowCoarseS13_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (576053399119267087 / 1000000000000000000) (149862337829405927 / 250000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS13_hz70 hx hc) (lowCoarseS13_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (576053399119267087 / 1000000000000000000) (149862337829405927 / 250000000000000000) (nlam x c) := by
    convert (lowCoarseS13_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS13_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS13_hz73 hx hc) (lowCoarseS13_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS13_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS13_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS13_hz3 hx hc) (lowCoarseS13_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS13_hz76 hx hc) (lowCoarseS13_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS13_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS13_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS13_hz80 hx hc) (lowCoarseS13_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS13_hz81 hx hc) (lowCoarseS13_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS13_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS13_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (2032081635970141 / 1000000000000000000) (21137602000560121 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS13_hz59 hx hc) (lowCoarseS13_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (101604081798507 / 100000000000000000) (1839560576075197 / 125000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS13_hz84 hx hc) (lowCoarseS13_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (165918759318430811 / 500000000000000000) (359339524795119853 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS13_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (317215114626425569 / 1000000000000000000) (334251016939078921 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS13_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (665748983060921079 / 1000000000000000000) (682784885373574431 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS13_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (815934423260179089 / 1000000000000000000) (165261596915142319 / 200000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS13_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (2563333589925203539 / 1000000000000000000) (648980773486410933 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS13_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (63915128959481031 / 500000000000000000) (70092227989257761 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS13_hz86 hx hc) (lowCoarseS13_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (32211574684236783 / 250000000000000000) (77450470293558549 / 500000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS13_hz85 hx hc) (lowCoarseS13_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS13_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (32211574684236783 / 250000000000000000) (154903815587117099 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS13_hz92 hx hc) (lowCoarseS13_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (32211574684236783 / 250000000000000000) (159724572311803313 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS13_hz94 hx hc) (lowCoarseS13_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (32211574684236783 / 250000000000000000) (159724572311803313 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS13_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS13_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (-7565331410655299 / 1000000000000000000) (11540188953934681 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS13_hz59 hx hc) (lowCoarseS13_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (-7565331410655299 / 1000000000000000000) 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS13_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (-1053431541202531 / 200000000000000000) 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS13_hz50 hx hc) (lowCoarseS13_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (-329377044125791 / 62500000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS13_hz99 hx hc) (lowCoarseS13_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (-1009078943069887 / 100000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS13_hz100 hx hc) (lowCoarseS13_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B (-1009078943069887 / 100000000000000000) 0 (nl x c) := by
    convert (lowCoarseS13_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS13_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (159724572311803313 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS13_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (1009078943069887 / 100000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS13_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (159724572311803313 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS13_hz103 hx hc) (lowCoarseS13_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS13_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) : B 0 (159724572311803313 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS13_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS13 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (43 / 100) (11 / 25) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS13_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS13_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS13_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS13_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS13_hz38 hx hc).1) (lowCoarseS13_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS13_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS13_hz55 hx hc).1,(lowCoarseS13_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS13_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS13_hz68 hx hc).2 (lowCoarseS13_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS13_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS13_hz55 hx hc).1,(lowCoarseS13_hz64 hx hc).2]

theorem lowCoarseS14_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS14_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (11 / 25) (9 / 20) c := hc

theorem lowCoarseS14_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS14_hz2 hx hc) (lowCoarseS14_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS14_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS14_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS14_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS14_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS14_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS14_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS14_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS14_hz10 hx hc) (lowCoarseS14_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS14_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS14_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (322510780936897579 / 500000000000000000) (645021561876114903 / 1000000000000000000) (kdot ((11 / 25))) := by
    constructor
    · apply bkdot_lower (q := (124721912892464713 / 200000000000000000)) (a := (557598826700032049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (155902391115580891 / 250000000000000000)) (a := (111519765339277641 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS14_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (121 / 625) (121 / 625) (((11 / 25) : ℝ)^2) := bsq (bpoint ((11 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (504 / 625) (504 / 625) ((1 : ℝ) - (((11 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS14_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (224499443206436483 / 250000000000000000) (897997772825745933 / 1000000000000000000) (√((1 : ℝ) - (((11 / 25) : ℝ)^2))) := bsqrt (lowCoarseS14_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (285841568861460699 / 1000000000000000000) (2858415688614607 / 10000000000000000) ((√((1 : ℝ) - (((11 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS14_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (283809487224469869 / 1000000000000000000) (141904743612745279 / 500000000000000000) (((11 / 25) : ℝ) * (kdot ((11 / 25)))) := bmul (bpoint ((11 / 25) : ℝ)) (lowCoarseS14_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (71206382010741321 / 125000000000000000) (284825528043475629 / 500000000000000000) (((√((1 : ℝ) - (((11 / 25) : ℝ)^2))) / Real.pi) + (((11 / 25) : ℝ) * (kdot ((11 / 25))))) := badd (lowCoarseS14_hz17 hx hc) (lowCoarseS14_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (71206382010741321 / 125000000000000000) (284825528043475629 / 500000000000000000) (kappa ((11 / 25))) := by rw [kappa_eq]; exact (lowCoarseS14_hz19 hx hc)

theorem lowCoarseS14_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (32428801097325763 / 50000000000000000) (64857602194777443 / 100000000000000000) (kdot ((9 / 20))) := by
    constructor
    · apply bkdot_lower (q := (307940881025719857 / 500000000000000000)) (a := (552015493874064193 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (615881762051439713 / 1000000000000000000)) (a := (276007746936043147 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS14_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (81 / 400) (81 / 400) (((9 / 20) : ℝ)^2) := bsq (bpoint ((9 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (319 / 400) (319 / 400) ((1 : ℝ) - (((9 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS14_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (13953571171477931 / 15625000000000000) (178605710994917517 / 200000000000000000) (√((1 : ℝ) - (((9 / 20) : ℝ)^2))) := bsqrt (lowCoarseS14_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (35532477211604503 / 125000000000000000) (11370392707713441 / 40000000000000000) ((√((1 : ℝ) - (((9 / 20) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS14_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (291859209875931867 / 1000000000000000000) (145929604938249247 / 500000000000000000) (((9 / 20) : ℝ) * (kdot ((9 / 20)))) := bmul (bpoint ((9 / 20) : ℝ)) (lowCoarseS14_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (576119027568767891 / 1000000000000000000) (576119027569334519 / 1000000000000000000) (((√((1 : ℝ) - (((9 / 20) : ℝ)^2))) / Real.pi) + (((9 / 20) : ℝ) * (kdot ((9 / 20))))) := badd (lowCoarseS14_hz25 hx hc) (lowCoarseS14_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (576119027568767891 / 1000000000000000000) (576119027569334519 / 1000000000000000000) (kappa ((9 / 20))) := by rw [kappa_eq]; exact (lowCoarseS14_hz27 hx hc)

theorem lowCoarseS14_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (71206382010741321 / 125000000000000000) (576119027569334519 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS14_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS14_hz20 hx hc).1 (lowCoarseS14_hz28 hx hc).2

theorem lowCoarseS14_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (423880972430665481 / 1000000000000000000) (53793617989258679 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS14_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (423880972430665481 / 500000000000000000) (53793617989258679 / 62500000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS14_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS14_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (423880909930665481 / 500000000000000000) (53793617989258679 / 62500000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS14_hz31 hx hc) (lowCoarseS14_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (920739822024295287 / 1000000000000000000) (927738049143258361 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS14_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS14_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS14_hz35 hx hc) (lowCoarseS14_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (229337164258183163 / 250000000000000000) (927738049143258361 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS14_hz34 hx hc) (lowCoarseS14_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (229337164258183163 / 250000000000000000) (927738049143258361 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS14_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS14_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS14_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS14_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (841528558559758157 / 1000000000000000000) (430348943914069433 / 500000000000000000) ((ndm x c)^2) := bsq (lowCoarseS14_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (569651056085930567 / 500000000000000000) (1165259521423367117 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS14_hz40 hx hc) (lowCoarseS14_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS14_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS14_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (569651056085930567 / 1000000000000000000) (584610609225990121 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS14_hz42 hx hc) (lowCoarseS14_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (569651056085930567 / 1000000000000000000) (584610609225990121 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS14_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS14_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (322510780936897579 / 500000000000000000) (64857602194777443 / 100000000000000000) (kdot c) := bkdot (lowCoarseS14_hz1 hx hc) (lowCoarseS14_hz13 hx hc).1 (lowCoarseS14_hz21 hx hc).2

theorem lowCoarseS14_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (346460823382203779 / 500000000000000000) (692921646764408003 / 1000000000000000000) (kdot ((569651056085930567 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (20944442452951229 / 40000000000000000)) (a := (120589387325173591 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (130902765330945181 / 250000000000000000)) (a := (482357549300693667 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS14_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (698752700562397617 / 1000000000000000000) (349376350281198883 / 500000000000000000) (kdot ((584610609225990121 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (31999739129086723 / 62500000000000000)) (a := (473198151413468149 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (511995826065387567 / 1000000000000000000)) (a := (118299537853366979 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS14_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (346460823382203779 / 500000000000000000) (349376350281198883 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS14_hz46 hx hc) (lowCoarseS14_hz48 hx hc).1 (lowCoarseS14_hz49 hx hc).2

theorem lowCoarseS14_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (121 / 625) (81 / 400) (c^2) := bsq (lowCoarseS14_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (319 / 400) (504 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS14_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (13953571171477931 / 15625000000000000) (897997772825745933 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS14_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (288011336663803413 / 500000000000000000) (582419823217283551 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS14_hz53 hx hc) (lowCoarseS14_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (288011336663803413 / 500000000000000000) (582419823217283551 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS14_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS14_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (35532477211604503 / 125000000000000000) (2858415688614607 / 10000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS14_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (283809487224469869 / 1000000000000000000) (145929604938249247 / 500000000000000000) (c * (kdot c)) := bmul (lowCoarseS14_hz1 hx hc) (lowCoarseS14_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-759939218366247 / 100000000000000000) (2032081636990831 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS14_hz56 hx hc) (lowCoarseS14_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-759939218366247 / 100000000000000000) (2032081636990831 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS14_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS14_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS14_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS14_hz3 hx hc) (lowCoarseS14_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS14_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS14_hz62 hx hc) (lowCoarseS14_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS14_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS14_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS14_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS14_hz65 hx hc) (lowCoarseS14_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS14_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS14_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS14_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS14_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (288011336663803413 / 500000000000000000) (59681594278722171 / 100000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS14_hz55 hx hc) (lowCoarseS14_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (288011336663803413 / 500000000000000000) (298914810785051729 / 500000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS14_hz69 hx hc) (lowCoarseS14_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (288011336663803413 / 500000000000000000) (74940650508235597 / 125000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS14_hz70 hx hc) (lowCoarseS14_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (288011336663803413 / 500000000000000000) (74940650508235597 / 125000000000000000) (nlam x c) := by
    convert (lowCoarseS14_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS14_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS14_hz73 hx hc) (lowCoarseS14_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS14_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS14_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS14_hz3 hx hc) (lowCoarseS14_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS14_hz76 hx hc) (lowCoarseS14_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS14_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS14_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS14_hz80 hx hc) (lowCoarseS14_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS14_hz81 hx hc) (lowCoarseS14_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS14_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS14_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-759939218366247 / 100000000000000000) (11629494683616271 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS14_hz59 hx hc) (lowCoarseS14_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-331880988185433 / 62500000000000000) (8126140816352917 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS14_hz84 hx hc) (lowCoarseS14_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (10368816255858839 / 31250000000000000) (22464404394390049 / 62500000000000000) ((nlam x c)^2) := bsq (lowCoarseS14_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (81125581424954003 / 250000000000000000) (170884782209791663 / 500000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS14_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (329115217790208337 / 500000000000000000) (168874418575045997 / 250000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS14_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (162262803572527573 / 200000000000000000) (102735831923143421 / 125000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS14_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (2548818158271681401 / 1000000000000000000) (2582033078641465049 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS14_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (12850420969899437 / 100000000000000000) (220341379802697 / 1562500000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS14_hz86 hx hc) (lowCoarseS14_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (61597056944013721 / 500000000000000000) (149144623890078997 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS14_hz85 hx hc) (lowCoarseS14_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS14_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (61597056944013721 / 500000000000000000) (74573749445039499 / 500000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS14_hz92 hx hc) (lowCoarseS14_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (61597056944013721 / 500000000000000000) (38492063903691303 / 250000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS14_hz94 hx hc) (lowCoarseS14_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (61597056944013721 / 500000000000000000) (38492063903691303 / 250000000000000000) (nu x c) := by
    convert (lowCoarseS14_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS14_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-1719680523028791 / 100000000000000000) (2032081636990831 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS14_hz59 hx hc) (lowCoarseS14_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-1719680523028791 / 100000000000000000) 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS14_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-3004078523927311 / 250000000000000000) 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS14_hz50 hx hc) (lowCoarseS14_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-2403837819141849 / 200000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS14_hz99 hx hc) (lowCoarseS14_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-16839945820395459 / 1000000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS14_hz100 hx hc) (lowCoarseS14_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B (-16839945820395459 / 1000000000000000000) 0 (nl x c) := by
    convert (lowCoarseS14_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS14_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (38492063903691303 / 250000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS14_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (16839945820395459 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS14_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (38492063903691303 / 250000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS14_hz103 hx hc) (lowCoarseS14_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS14_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) : B 0 (38492063903691303 / 250000000000000000) (ns x c) := by
    convert (lowCoarseS14_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS14 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (11 / 25) (9 / 20) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS14_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS14_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS14_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS14_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS14_hz38 hx hc).1) (lowCoarseS14_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS14_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS14_hz55 hx hc).1,(lowCoarseS14_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS14_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS14_hz68 hx hc).2 (lowCoarseS14_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS14_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS14_hz55 hx hc).1,(lowCoarseS14_hz64 hx hc).2]

theorem lowCoarseS15_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS15_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (9 / 20) (23 / 50) c := hc

theorem lowCoarseS15_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS15_hz2 hx hc) (lowCoarseS15_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS15_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS15_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS15_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS15_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS15_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS15_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS15_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS15_hz10 hx hc) (lowCoarseS15_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS15_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS15_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (32428801097325763 / 50000000000000000) (64857602194777443 / 100000000000000000) (kdot ((9 / 20))) := by
    constructor
    · apply bkdot_lower (q := (307940881025719857 / 500000000000000000)) (a := (552015493874064193 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (615881762051439713 / 1000000000000000000)) (a := (276007746936043147 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS15_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (81 / 400) (81 / 400) (((9 / 20) : ℝ)^2) := bsq (bpoint ((9 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (319 / 400) (319 / 400) ((1 : ℝ) - (((9 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS15_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (13953571171477931 / 15625000000000000) (178605710994917517 / 200000000000000000) (√((1 : ℝ) - (((9 / 20) : ℝ)^2))) := bsqrt (lowCoarseS15_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (35532477211604503 / 125000000000000000) (11370392707713441 / 40000000000000000) ((√((1 : ℝ) - (((9 / 20) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS15_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (291859209875931867 / 1000000000000000000) (145929604938249247 / 500000000000000000) (((9 / 20) : ℝ) * (kdot ((9 / 20)))) := bmul (bpoint ((9 / 20) : ℝ)) (lowCoarseS15_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (576119027568767891 / 1000000000000000000) (576119027569334519 / 1000000000000000000) (((√((1 : ℝ) - (((9 / 20) : ℝ)^2))) / Real.pi) + (((9 / 20) : ℝ) * (kdot ((9 / 20))))) := badd (lowCoarseS15_hz17 hx hc) (lowCoarseS15_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (576119027568767891 / 1000000000000000000) (576119027569334519 / 1000000000000000000) (kappa ((9 / 20))) := by rw [kappa_eq]; exact (lowCoarseS15_hz19 hx hc)

theorem lowCoarseS15_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (163037649309219301 / 250000000000000000) (326075298618777983 / 500000000000000000) (kdot ((23 / 50))) := by
    constructor
    · apply bkdot_lower (q := (121632728111907469 / 200000000000000000)) (a := (10928011282762237 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (9502556883742771 / 15625000000000000)) (a := (273200282068522827 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS15_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (529 / 2500) (529 / 2500) (((23 / 50) : ℝ)^2) := bsq (bpoint ((23 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (1971 / 2500) (1971 / 2500) ((1 : ℝ) - (((23 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS15_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (887918915216924523 / 1000000000000000000) (221979728804231131 / 250000000000000000) (√((1 : ℝ) - (((23 / 50) : ℝ)^2))) := bsqrt (lowCoarseS15_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (282633368843134123 / 1000000000000000000) (2261066950745073 / 8000000000000000) ((√((1 : ℝ) - (((23 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS15_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (299989274728963513 / 1000000000000000000) (59997854945855149 / 200000000000000000) (((23 / 50) : ℝ) * (kdot ((23 / 50)))) := bmul (bpoint ((23 / 50) : ℝ)) (lowCoarseS15_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (145655660893024409 / 250000000000000000) (58262264357240987 / 100000000000000000) (((√((1 : ℝ) - (((23 / 50) : ℝ)^2))) / Real.pi) + (((23 / 50) : ℝ) * (kdot ((23 / 50))))) := badd (lowCoarseS15_hz25 hx hc) (lowCoarseS15_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (145655660893024409 / 250000000000000000) (58262264357240987 / 100000000000000000) (kappa ((23 / 50))) := by rw [kappa_eq]; exact (lowCoarseS15_hz27 hx hc)

theorem lowCoarseS15_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (576119027568767891 / 1000000000000000000) (58262264357240987 / 100000000000000000) (kappa c) := bkappa (lowCoarseS15_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS15_hz20 hx hc).1 (lowCoarseS15_hz28 hx hc).2

theorem lowCoarseS15_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (41737735642759013 / 100000000000000000) (423880972431232109 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS15_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (41737735642759013 / 50000000000000000) (423880972431232109 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS15_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS15_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (41737729392759013 / 50000000000000000) (423880972431232109 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS15_hz31 hx hc) (lowCoarseS15_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (114206131338195637 / 125000000000000000) (920739889905104643 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS15_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS15_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS15_hz35 hx hc) (lowCoarseS15_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (910257885714002461 / 1000000000000000000) (920739889905104643 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS15_hz34 hx hc) (lowCoarseS15_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (910257885714002461 / 1000000000000000000) (920739889905104643 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS15_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS15_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS15_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS15_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (165713883700905193 / 200000000000000000) (847761944862464219 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS15_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (1152238055137535781 / 1000000000000000000) (1178218661478599309 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS15_hz40 hx hc) (lowCoarseS15_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS15_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS15_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (57611902756876789 / 100000000000000000) (147778052190267641 / 250000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS15_hz42 hx hc) (lowCoarseS15_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (57611902756876789 / 100000000000000000) (147778052190267641 / 250000000000000000) (nc1 x c) := by
    convert (lowCoarseS15_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS15_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (32428801097325763 / 50000000000000000) (326075298618777983 / 500000000000000000) (kdot c) := bkdot (lowCoarseS15_hz1 hx hc) (lowCoarseS15_hz13 hx hc).1 (lowCoarseS15_hz21 hx hc).2

theorem lowCoarseS15_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (347716766946063269 / 500000000000000000) (21732297934128963 / 31250000000000000) (kdot ((57611902756876789 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (64824245101235471 / 125000000000000000)) (a := (478411886227150007 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (518593960809883767 / 1000000000000000000)) (a := (119602971556787393 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS15_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (701310964952475547 / 1000000000000000000) (701310964952475641 / 1000000000000000000) (kdot ((147778052190267641 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (495053016325017 / 976562500000000)) (a := (469179639106563549 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (506934288716817407 / 1000000000000000000)) (a := (117294909776640851 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS15_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (347716766946063269 / 500000000000000000) (701310964952475641 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS15_hz46 hx hc) (lowCoarseS15_hz48 hx hc).1 (lowCoarseS15_hz49 hx hc).2

theorem lowCoarseS15_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (81 / 400) (529 / 2500) (c^2) := bsq (lowCoarseS15_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (1971 / 2500) (319 / 400) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS15_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (887918915216924523 / 1000000000000000000) (178605710994917517 / 200000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS15_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (575882917842458061 / 1000000000000000000) (4659112843814951 / 8000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS15_hz53 hx hc) (lowCoarseS15_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (575882917842458061 / 1000000000000000000) (4659112843814951 / 8000000000000000) (npa c) := by
    convert (lowCoarseS15_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS15_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (282633368843134123 / 1000000000000000000) (11370392707713441 / 40000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS15_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (291859209875931867 / 1000000000000000000) (59997854945855149 / 200000000000000000) (c * (kdot c)) := bmul (lowCoarseS15_hz1 hx hc) (lowCoarseS15_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-8677952943070811 / 500000000000000000) (-3799696091547921 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS15_hz56 hx hc) (lowCoarseS15_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-8677952943070811 / 500000000000000000) (-3799696091547921 / 500000000000000000) (npp c) := by
    convert (lowCoarseS15_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS15_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS15_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS15_hz3 hx hc) (lowCoarseS15_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS15_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS15_hz62 hx hc) (lowCoarseS15_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS15_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS15_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS15_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS15_hz65 hx hc) (lowCoarseS15_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS15_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS15_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS15_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS15_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (575882917842458061 / 1000000000000000000) (298392612523403517 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS15_hz55 hx hc) (lowCoarseS15_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (575882917842458061 / 1000000000000000000) (74724856457035091 / 125000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS15_hz69 hx hc) (lowCoarseS15_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (575882917842458061 / 1000000000000000000) (299747217076031023 / 500000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS15_hz70 hx hc) (lowCoarseS15_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (575882917842458061 / 1000000000000000000) (299747217076031023 / 500000000000000000) (nlam x c) := by
    convert (lowCoarseS15_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS15_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS15_hz73 hx hc) (lowCoarseS15_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS15_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS15_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS15_hz3 hx hc) (lowCoarseS15_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS15_hz76 hx hc) (lowCoarseS15_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS15_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS15_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS15_hz80 hx hc) (lowCoarseS15_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS15_hz81 hx hc) (lowCoarseS15_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS15_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS15_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-8677952943070811 / 500000000000000000) (999010431764799 / 500000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS15_hz59 hx hc) (lowCoarseS15_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-12171887104634333 / 1000000000000000000) (700616969898561 / 500000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS15_hz84 hx hc) (lowCoarseS15_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (3316411350627433 / 10000000000000000) (359393576579301057 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS15_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (20744570870423921 / 62500000000000000) (87353410836597867 / 250000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS15_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (162646589163402133 / 250000000000000000) (41755429129576079 / 62500000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS15_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (806589335816937597 / 1000000000000000000) (81736580921470973 / 100000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS15_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (633493782966590461 / 250000000000000000) (513566084304881723 / 200000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS15_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (129152272783598561 / 1000000000000000000) (70914977037401911 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS15_hz86 hx hc) (lowCoarseS15_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (29245096419741057 / 250000000000000000) (8951949250912559 / 62500000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS15_hz85 hx hc) (lowCoarseS15_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS15_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (29245096419741057 / 250000000000000000) (28646812602920189 / 200000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS15_hz92 hx hc) (lowCoarseS15_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (29245096419741057 / 250000000000000000) (148054819739287159 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS15_hz94 hx hc) (lowCoarseS15_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (29245096419741057 / 250000000000000000) (148054819739287159 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS15_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS15_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-13476659466383531 / 500000000000000000) (-3799696091547921 / 500000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS15_hz59 hx hc) (lowCoarseS15_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-13476659466383531 / 500000000000000000) (-3799696091547921 / 500000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS15_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-189026581094107 / 10000000000000000) (-5284872161322543 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS15_hz50 hx hc) (lowCoarseS15_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-18905533109410701 / 1000000000000000000) (-5284872161322543 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS15_hz99 hx hc) (lowCoarseS15_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-4745257966819383 / 200000000000000000) (-5284872161322543 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS15_hz100 hx hc) (lowCoarseS15_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B (-4745257966819383 / 200000000000000000) (-5284872161322543 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS15_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS15_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (148054819739287159 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS15_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (4745257966819383 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS15_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (148054819739287159 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS15_hz103 hx hc) (lowCoarseS15_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS15_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) : B 0 (148054819739287159 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS15_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS15 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (9 / 20) (23 / 50) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS15_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS15_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS15_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS15_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS15_hz38 hx hc).1) (lowCoarseS15_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS15_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS15_hz55 hx hc).1,(lowCoarseS15_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS15_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS15_hz68 hx hc).2 (lowCoarseS15_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS15_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS15_hz55 hx hc).1,(lowCoarseS15_hz64 hx hc).2]

end BstLean.BlueprintLow
