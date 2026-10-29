import BstLean.Part281Normalize
namespace BstLean.Part281.TI
open BstLean.Part264b
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
theorem normalizedE52W_hz0 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (1 / 11883) x := _hx

theorem normalizedE52W_hz1 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (69609039 / 200000000) (636843189 / 1000000000) c := _hc

theorem normalizedE52W_hz2 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz3 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz4 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz5 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (114151813231091 / 100000000000000000) ((√(184 : ℝ)) * x) := bmul (normalizedE52W_hz2 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz6 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 1 (100114151813231091 / 100000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (normalizedE52W_hz5 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz7 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 1 (100114151813231091 / 100000000000000000) (nap x) := by
    convert (normalizedE52W_hz6 _hx _hc) using 1 <;>
      norm_num [nap] <;> ring

theorem normalizedE52W_hz8 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (1770466911 / 250000000000000000) (x^2) := bsq (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz9 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (1770466911 / 125000000000000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz8 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz10 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (124999998229533089 / 125000000000000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (normalizedE52W_hz9 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz11 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (99999999291813233 / 100000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (normalizedE52W_hz10 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz12 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (49942923739291071 / 50000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (normalizedE52W_hz11 _hx _hc) (normalizedE52W_hz5 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz13 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (49942923739291071 / 50000000000000000) 1 (nam x) := by
    convert (normalizedE52W_hz12 _hx _hc) using 1 <;>
      norm_num [nam] <;> ring

theorem normalizedE52W_hz14 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (306577213940453543 / 500000000000000000) (306577214182697789 / 500000000000000000) (kdot ((69609039 / 200000000))) := by
    constructor
    · apply bkdot_lower (q := (347717479752617833 / 500000000000000000)) (a := (30382780186077071 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (139086991901047133 / 200000000000000000)) (a := (607655602960508679 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52W_hz15 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (4845418310503521 / 40000000000000000) (4845418310503521 / 40000000000000000) (((69609039 / 200000000) : ℝ)^2) := bsq (bpoint ((69609039 / 200000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz16 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (35154581689496479 / 40000000000000000) (35154581689496479 / 40000000000000000) ((1 : ℝ) - (((69609039 / 200000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (normalizedE52W_hz15 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz17 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (234369438899013129 / 250000000000000000) (937477755596052517 / 1000000000000000000) (√((1 : ℝ) - (((69609039 / 200000000) : ℝ)^2))) := bsqrt (normalizedE52W_hz16 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz18 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (74602109420903751 / 250000000000000000) (59681687536723001 / 200000000000000000) ((√((1 : ℝ) - (((69609039 / 200000000) : ℝ)^2))) / Real.pi) := bdiv (normalizedE52W_hz17 _hx _hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz19 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (213405452416923743 / 1000000000000000000) (53351363146386909 / 250000000000000000) (((69609039 / 200000000) : ℝ) * (kdot ((69609039 / 200000000)))) := bmul (bpoint ((69609039 / 200000000) : ℝ)) (normalizedE52W_hz14 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz20 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (511813890100538747 / 1000000000000000000) (511813890269162641 / 1000000000000000000) (((√((1 : ℝ) - (((69609039 / 200000000) : ℝ)^2))) / Real.pi) + (((69609039 / 200000000) : ℝ) * (kdot ((69609039 / 200000000))))) := badd (normalizedE52W_hz18 _hx _hc) (normalizedE52W_hz19 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz21 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (511813890100538747 / 1000000000000000000) (511813890269162641 / 1000000000000000000) (kappa ((69609039 / 200000000))) := by rw [kappa_eq]; exact (normalizedE52W_hz20 _hx _hc)

theorem normalizedE52W_hz22 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (359880068880798849 / 500000000000000000) (719760137761597703 / 1000000000000000000) (kdot ((636843189 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (9420491341419919 / 20000000000000000)) (a := (44019974622559019 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (471024567070995949 / 1000000000000000000)) (a := (55024968278198773 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52W_hz23 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (405569247375689721 / 1000000000000000000) (405569247375689721 / 1000000000000000000) (((636843189 / 1000000000) : ℝ)^2) := bsq (bpoint ((636843189 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz24 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (594430752624310279 / 1000000000000000000) (594430752624310279 / 1000000000000000000) ((1 : ℝ) - (((636843189 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (normalizedE52W_hz23 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz25 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (770993354461833399 / 1000000000000000000) (3854966772309167 / 5000000000000000) (√((1 : ℝ) - (((636843189 / 1000000000) : ℝ)^2))) := bsqrt (normalizedE52W_hz24 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz26 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (122707403453602583 / 500000000000000000) (15338425431700323 / 62500000000000000) ((√((1 : ℝ) - (((636843189 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (normalizedE52W_hz25 _hx _hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz27 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (458374341447175199 / 1000000000000000000) (458374341447175203 / 1000000000000000000) (((636843189 / 1000000000) : ℝ) * (kdot ((636843189 / 1000000000)))) := bmul (bpoint ((636843189 / 1000000000) : ℝ)) (normalizedE52W_hz22 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz28 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (140757829670876073 / 200000000000000000) (703789148354380371 / 1000000000000000000) (((√((1 : ℝ) - (((636843189 / 1000000000) : ℝ)^2))) / Real.pi) + (((636843189 / 1000000000) : ℝ) * (kdot ((636843189 / 1000000000))))) := badd (normalizedE52W_hz26 _hx _hc) (normalizedE52W_hz27 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz29 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (140757829670876073 / 200000000000000000) (703789148354380371 / 1000000000000000000) (kappa ((636843189 / 1000000000))) := by rw [kappa_eq]; exact (normalizedE52W_hz28 _hx _hc)

theorem normalizedE52W_hz30 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (511813890100538747 / 1000000000000000000) (703789148354380371 / 1000000000000000000) (kappa c) := bkappa (normalizedE52W_hz1 _hx _hc) (by norm_num) (by norm_num) (normalizedE52W_hz21 _hx _hc).1 (normalizedE52W_hz29 _hx _hc).2

theorem normalizedE52W_hz31 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (296210851645619629 / 1000000000000000000) (488186109899461253 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (normalizedE52W_hz30 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz32 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (296210851645619629 / 500000000000000000) (488186109899461253 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz31 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz33 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (1770466911 / 31250000000000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (normalizedE52W_hz8 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz34 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (296210823318149053 / 500000000000000000) (488186109899461253 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (normalizedE52W_hz32 _hx _hc) (normalizedE52W_hz33 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz35 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (384844659127646627 / 500000000000000000) (24702887227494817 / 25000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (normalizedE52W_hz34 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz36 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz2 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz37 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (2283036264621819 / 1000000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (normalizedE52W_hz36 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz38 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (153481256398134287 / 200000000000000000) (24702887227494817 / 25000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (normalizedE52W_hz35 _hx _hc) (normalizedE52W_hz37 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz39 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (153481256398134287 / 200000000000000000) (24702887227494817 / 25000000000000000) (ndm x c) := by
    convert (normalizedE52W_hz38 _hx _hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem normalizedE52W_hz40 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 1 (200456867865653643 / 200000000000000000) ((nap x)^2) := bsq (normalizedE52W_hz7 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz41 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 2 (200456867865653643 / 100000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz40 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz42 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (23556496065549837 / 40000000000000000) (976372219798922507 / 1000000000000000000) ((ndm x c)^2) := bsq (normalizedE52W_hz39 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz43 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (1023627780201077493 / 1000000000000000000) (283131255403558101 / 200000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (normalizedE52W_hz41 _hx _hc) (normalizedE52W_hz42 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz44 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (199543650530291489 / 200000000000000000) 1 ((nam x)^2) := bsq (normalizedE52W_hz13 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz45 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (199543650530291489 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz44 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz46 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (255906945050269373 / 500000000000000000) (35472345856549529 / 50000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (normalizedE52W_hz43 _hx _hc) (normalizedE52W_hz45 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz47 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (255906945050269373 / 500000000000000000) (35472345856549529 / 50000000000000000) (nc1 x c) := by
    convert (normalizedE52W_hz46 _hx _hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem normalizedE52W_hz48 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (167756566326578971 / 250000000000000000) (167756566326585071 / 250000000000000000) (kdot ((255906945050269373 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (284127681838300519 / 500000000000000000)) (a := (258375367034418927 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (568255363676601037 / 1000000000000000000)) (a := (64593841758599941 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52W_hz49 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (375527591078360987 / 500000000000000000) (93881897769590247 / 125000000000000000) (kdot ((35472345856549529 / 50000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (16490921545528813 / 40000000000000000)) (a := (391041605442845761 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (103068259659555081 / 250000000000000000)) (a := (391041605442845759 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52W_hz50 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (167756566326578971 / 250000000000000000) (93881897769590247 / 125000000000000000) (kdot (nc1 x c)) := bkdot (normalizedE52W_hz47 _hx _hc) (normalizedE52W_hz48 _hx _hc).1 (normalizedE52W_hz49 _hx _hc).2

theorem normalizedE52W_hz51 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz52 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (25224225381389 / 62500000000000000) ((√(23 : ℝ)) * x) := bmul (normalizedE52W_hz51 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz53 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (1 / 2) (31275224225381389 / 62500000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (normalizedE52W_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz54 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (167756566326578971 / 500000000000000000) (93881897769590247 / 250000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (normalizedE52W_hz50 _hx _hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz55 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (167756566326578971 / 500000000000000000) (93982794671115803 / 250000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (normalizedE52W_hz54 _hx _hc) (normalizedE52W_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz56 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (359880068880798849 / 1000000000000000000) (89970017220199713 / 250000000000000000) ((kdot ((636843189 / 1000000000))) / (2 : ℝ)) := bdiv (normalizedE52W_hz22 _hx _hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz57 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (359880068880798849 / 1000000000000000000) (90070914121725269 / 250000000000000000) (((kdot ((636843189 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (normalizedE52W_hz56 _hx _hc) (normalizedE52W_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz58 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (176848025788758493 / 250000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52W_hz53 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz59 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (4586769920300739 / 500000000000000000) (√x) := bsqrt (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz60 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (14331312859912709 / 20000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (normalizedE52W_hz58 _hx _hc) (normalizedE52W_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz61 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (807175212204447 / 1000000000000000000) ((√(92 : ℝ)) * x) := bmul (normalizedE52W_hz3 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz62 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (717372818207839897 / 1000000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52W_hz60 _hx _hc) (normalizedE52W_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz63 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (253629592196833991 / 250000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz62 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz64 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (253629592196833991 / 250000000000000000) (neb x (1/2+√23*x)) := by
    convert (normalizedE52W_hz63 _hx _hc) using 1 <;>
      norm_num [neb] <;> ring

theorem normalizedE52W_hz65 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (299950024537754809 / 500000000000000000) (120047266772201203 / 200000000000000000) (√(((kdot ((636843189 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52W_hz57 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz66 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (299950024537754809 / 500000000000000000) (609409873701607493 / 1000000000000000000) ((√(((kdot ((636843189 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (normalizedE52W_hz65 _hx _hc) (normalizedE52W_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz67 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (299950024537754809 / 500000000000000000) (30510852445690597 / 50000000000000000) (((√(((kdot ((636843189 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52W_hz66 _hx _hc) (normalizedE52W_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz68 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (848386785470871001 / 1000000000000000000) (34519089062607967 / 40000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((636843189 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz67 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz69 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (848386785470871001 / 1000000000000000000) (34519089062607967 / 40000000000000000) (neb x (kdot (636843189 / 1000000000)/2+√23*x)) := by
    convert (normalizedE52W_hz68 _hx _hc) using 1 <;>
      norm_num [neb] <;> ring

theorem normalizedE52W_hz70 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (12973344457548531 / 1000000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz71 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 1 (1012973344457548531 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (normalizedE52W_hz70 _hx _hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem normalizedE52W_hz72 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (43994751547921709 / 500000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (normalizedE52W_hz3 _hx _hc) (normalizedE52W_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz73 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 1 (1100962847553391949 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (normalizedE52W_hz71 _hx _hc) (normalizedE52W_hz72 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz74 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1556996590678909201 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz73 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz75 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1556996590678909201 / 1000000000000000000) (np1 x) := by
    convert (normalizedE52W_hz74 _hx _hc) using 1 <;>
      norm_num [np1] <;> ring

theorem normalizedE52W_hz76 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz3 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz77 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (185237340890323 / 200000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (normalizedE52W_hz76 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz78 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 1 (200185237340890323 / 200000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (normalizedE52W_hz77 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz79 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (283104677634364033 / 200000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz78 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz80 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (275495636176222773 / 125000000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (normalizedE52W_hz79 _hx _hc) (normalizedE52W_hz75 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz81 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (275495636176222773 / 125000000000000000) (ntf x (np1 x)) := by
    convert (normalizedE52W_hz80 _hx _hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem normalizedE52W_hz82 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (71359345341532179 / 50000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (normalizedE52W_hz70 _hx _hc) (normalizedE52W_hz4 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz83 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (757588204963243499 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (normalizedE52W_hz82 _hx _hc) (normalizedE52W_hz72 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz84 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2142783028305814153 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz83 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz85 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2142783028305814153 / 1000000000000000000) (nz x) := by
    convert (normalizedE52W_hz84 _hx _hc) using 1 <;>
      norm_num [nz] <;> ring

theorem normalizedE52W_hz86 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (579234954619589529 / 1000000000000000000) (613132268506937427 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52W_hz55 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz87 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (579234954619589529 / 500000000000000000) (613132268506937427 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz86 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz88 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (6890259834876489 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52W_hz70 _hx _hc) (normalizedE52W_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz89 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (2112320321580029 / 125000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52W_hz87 _hx _hc) (normalizedE52W_hz88 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz90 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (189902722368449 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (normalizedE52W_hz88 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz91 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (17088465295008681 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (normalizedE52W_hz89 _hx _hc) (normalizedE52W_hz90 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz92 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (17088465295008681 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz91 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz93 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (17088465295008681 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (normalizedE52W_hz92 _hx _hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem normalizedE52W_hz94 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (4857462115337069177 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (normalizedE52W_hz81 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz95 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (51096757082987 / 125000000000000000) (((ntf x (np1 x))^2) * x) := bmul (normalizedE52W_hz94 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz96 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (275495636176222773 / 62500000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz81 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz97 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (9445237977131575037 / 1000000000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (normalizedE52W_hz96 _hx _hc) (normalizedE52W_hz85 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz98 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1197795928170965297 / 125000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (normalizedE52W_hz97 _hx _hc) (normalizedE52W_hz64 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz99 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (806392950043569 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (normalizedE52W_hz98 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz100 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (243033401341493 / 200000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (normalizedE52W_hz95 _hx _hc) (normalizedE52W_hz99 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz101 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (51462376030345851 / 50000000000000000) ((neb x (1/2+√23*x))^2) := bsq (normalizedE52W_hz64 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz102 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (8794130267932517 / 250000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (normalizedE52W_hz93 _hx _hc) (normalizedE52W_hz101 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz103 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (36391688078437533 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (normalizedE52W_hz100 _hx _hc) (normalizedE52W_hz102 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz104 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (167756566326578971 / 250000000000000000) (93982794671115803 / 125000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz55 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz105 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (359880068880798847 / 500000000000000000) (744729693570163109 / 1000000000000000000) ((neb x (kdot (636843189 / 1000000000)/2+√23*x))^2) := bsq (normalizedE52W_hz69 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz106 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2424238383385746723 / 1000000000000000000) ((np1 x)^2) := bsq (normalizedE52W_hz75 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz107 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B 0 (204008952569701 / 1000000000000000000) (((np1 x)^2) * x) := bmul (normalizedE52W_hz106 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz108 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (359880068880798847 / 500000000000000000) (74493370252273281 / 100000000000000000) (((neb x (kdot (636843189 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (normalizedE52W_hz105 _hx _hc) (normalizedE52W_hz107 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz109 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (482977957158524323 / 1000000000000000000) (35005475603894029 / 62500000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (636843189 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (normalizedE52W_hz104 _hx _hc) (normalizedE52W_hz108 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz110 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (482977957158524323 / 1000000000000000000) (596479297740741997 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (636843189 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (normalizedE52W_hz103 _hx _hc) (normalizedE52W_hz109 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz111 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) : B (482977957158524323 / 1000000000000000000) (596479297740741997 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (636843189 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (normalizedE52W_hz110 _hx _hc) using 1 <;>
      norm_num [ne] <;> ring

theorem normalizedE52W {x c : ℝ}
    (_hx : B 0 (1/11883) x) (_hc : B (69609039 / 200000000) (636843189 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (636843189 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (1864 / 3125) :=
  (normalizedE52W_hz111 _hx _hc).2.trans (by norm_num)

theorem normalizedE52C_hz0 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (1 / 11883) x := _hx

theorem normalizedE52C_hz1 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (206684003 / 500000000) (68497037 / 125000000) c := _hc

theorem normalizedE52C_hz2 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz3 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz4 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz5 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (114151813231091 / 100000000000000000) ((√(184 : ℝ)) * x) := bmul (normalizedE52C_hz2 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz6 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 1 (100114151813231091 / 100000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (normalizedE52C_hz5 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz7 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 1 (100114151813231091 / 100000000000000000) (nap x) := by
    convert (normalizedE52C_hz6 _hx _hc) using 1 <;>
      norm_num [nap] <;> ring

theorem normalizedE52C_hz8 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (1770466911 / 250000000000000000) (x^2) := bsq (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz9 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (1770466911 / 125000000000000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz8 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz10 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (124999998229533089 / 125000000000000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (normalizedE52C_hz9 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz11 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (99999999291813233 / 100000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (normalizedE52C_hz10 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz12 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (49942923739291071 / 50000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (normalizedE52C_hz11 _hx _hc) (normalizedE52C_hz5 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz13 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (49942923739291071 / 50000000000000000) 1 (nam x) := by
    convert (normalizedE52C_hz12 _hx _hc) using 1 <;>
      norm_num [nam] <;> ring

theorem normalizedE52C_hz14 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (127129537797339573 / 200000000000000000) (79455961124767217 / 125000000000000000) (kdot ((206684003 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (322125606171588281 / 500000000000000000)) (a := (2289293087195707 / 4000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (644251212343176561 / 1000000000000000000)) (a := (114464654356191409 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52C_hz15 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (42718277096104009 / 250000000000000000) (42718277096104009 / 250000000000000000) (((206684003 / 500000000) : ℝ)^2) := bsq (bpoint ((206684003 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz16 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (207281722903895991 / 250000000000000000) (207281722903895991 / 250000000000000000) ((1 : ℝ) - (((206684003 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (normalizedE52C_hz15 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz17 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (227641012838139511 / 250000000000000000) (182112810270511609 / 200000000000000000) (√((1 : ℝ) - (((206684003 / 500000000) : ℝ)^2))) := bsqrt (normalizedE52C_hz16 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz18 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (11593661581963363 / 40000000000000000) (72460384887271019 / 250000000000000000) ((√((1 : ℝ) - (((206684003 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (normalizedE52C_hz17 _hx _hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz19 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (4105569026795929 / 15625000000000000) (131378208859834167 / 500000000000000000) (((206684003 / 500000000) : ℝ) * (kdot ((206684003 / 500000000)))) := bmul (bpoint ((206684003 / 500000000) : ℝ)) (normalizedE52C_hz14 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz20 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (552597957264023531 / 1000000000000000000) (55259795726875241 / 100000000000000000) (((√((1 : ℝ) - (((206684003 / 500000000) : ℝ)^2))) / Real.pi) + (((206684003 / 500000000) : ℝ) * (kdot ((206684003 / 500000000))))) := badd (normalizedE52C_hz18 _hx _hc) (normalizedE52C_hz19 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz21 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (552597957264023531 / 1000000000000000000) (55259795726875241 / 100000000000000000) (kappa ((206684003 / 500000000))) := by rw [kappa_eq]; exact (normalizedE52C_hz20 _hx _hc)

theorem normalizedE52C_hz22 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (684601604961798881 / 1000000000000000000) (342300802480900479 / 500000000000000000) (kdot ((68497037 / 125000000))) := by
    constructor
    · apply bkdot_lower (q := (27018949284993511 / 50000000000000000)) (a := (99085328080602413 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (540378985699870219 / 1000000000000000000)) (a := (123856660100752201 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52C_hz23 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (4691844077779369 / 15625000000000000) (4691844077779369 / 15625000000000000) (((68497037 / 125000000) : ℝ)^2) := bsq (bpoint ((68497037 / 125000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz24 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (10933155922220631 / 15625000000000000) (10933155922220631 / 15625000000000000) ((1 : ℝ) - (((68497037 / 125000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (normalizedE52C_hz23 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz25 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (83649386071992207 / 100000000000000000) (836493860719922071 / 1000000000000000000) (√((1 : ℝ) - (((68497037 / 125000000) : ℝ)^2))) := bsqrt (normalizedE52C_hz24 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz26 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (6656606639979951 / 25000000000000000) (266264265599198041 / 1000000000000000000) ((√((1 : ℝ) - (((68497037 / 125000000) : ℝ)^2))) / Real.pi) := bdiv (normalizedE52C_hz25 _hx _hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz27 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (93786362930655443 / 250000000000000000) (375145451722622911 / 1000000000000000000) (((68497037 / 125000000) : ℝ) * (kdot ((68497037 / 125000000)))) := bmul (bpoint ((68497037 / 125000000) : ℝ)) (normalizedE52C_hz22 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz28 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (160352429330454953 / 250000000000000000) (80176214665227619 / 125000000000000000) (((√((1 : ℝ) - (((68497037 / 125000000) : ℝ)^2))) / Real.pi) + (((68497037 / 125000000) : ℝ) * (kdot ((68497037 / 125000000))))) := badd (normalizedE52C_hz26 _hx _hc) (normalizedE52C_hz27 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz29 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (160352429330454953 / 250000000000000000) (80176214665227619 / 125000000000000000) (kappa ((68497037 / 125000000))) := by rw [kappa_eq]; exact (normalizedE52C_hz28 _hx _hc)

theorem normalizedE52C_hz30 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (552597957264023531 / 1000000000000000000) (80176214665227619 / 125000000000000000) (kappa c) := bkappa (normalizedE52C_hz1 _hx _hc) (by norm_num) (by norm_num) (normalizedE52C_hz21 _hx _hc).1 (normalizedE52C_hz29 _hx _hc).2

theorem normalizedE52C_hz31 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (44823785334772381 / 125000000000000000) (447402042735976469 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (normalizedE52C_hz30 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz32 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (44823785334772381 / 62500000000000000) (447402042735976469 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz31 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz33 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (1770466911 / 31250000000000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (normalizedE52C_hz8 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz34 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (44823781793838559 / 62500000000000000) (447402042735976469 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (normalizedE52C_hz32 _hx _hc) (normalizedE52C_hz33 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz35 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (105858138319449203 / 125000000000000000) (945940846708689781 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (normalizedE52C_hz34 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz36 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz2 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz37 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (2283036264621819 / 1000000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (normalizedE52C_hz36 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz38 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (168916414058194361 / 200000000000000000) (945940846708689781 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (normalizedE52C_hz35 _hx _hc) (normalizedE52C_hz37 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz39 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (168916414058194361 / 200000000000000000) (945940846708689781 / 1000000000000000000) (ndm x c) := by
    convert (normalizedE52C_hz38 _hx _hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem normalizedE52C_hz40 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 1 (200456867865653643 / 200000000000000000) ((nap x)^2) := bsq (normalizedE52C_hz7 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz41 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 2 (200456867865653643 / 100000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz40 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz42 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (356659436728492019 / 500000000000000000) (894804085471952939 / 1000000000000000000) ((ndm x c)^2) := bsq (normalizedE52C_hz39 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz43 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (1105195914528047061 / 1000000000000000000) (161406225649944049 / 125000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (normalizedE52C_hz41 _hx _hc) (normalizedE52C_hz42 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz44 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (199543650530291489 / 200000000000000000) 1 ((nam x)^2) := bsq (normalizedE52C_hz13 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz45 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (199543650530291489 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz44 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz46 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (55259795726402353 / 100000000000000000) (647101424559502953 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (normalizedE52C_hz43 _hx _hc) (normalizedE52C_hz45 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz47 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (55259795726402353 / 100000000000000000) (647101424559502953 / 1000000000000000000) (nc1 x c) := by
    convert (normalizedE52C_hz46 _hx _hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem normalizedE52C_hz48 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (686363482769833951 / 1000000000000000000) (171590870692458863 / 250000000000000000) (kdot ((55259795726402353 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (536808613885296461 / 1000000000000000000)) (a := (492659089213889133 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (26840430694264823 / 50000000000000000)) (a := (61582386151735847 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52C_hz49 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (724018980690561217 / 1000000000000000000) (36200949034528061 / 50000000000000000) (kdot ((647101424559502953 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (115719031414985967 / 250000000000000000)) (a := (108377492849094469 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (462876125659943867 / 1000000000000000000)) (a := (27094373212273617 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52C_hz50 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (686363482769833951 / 1000000000000000000) (36200949034528061 / 50000000000000000) (kdot (nc1 x c)) := bkdot (normalizedE52C_hz47 _hx _hc) (normalizedE52C_hz48 _hx _hc).1 (normalizedE52C_hz49 _hx _hc).2

theorem normalizedE52C_hz51 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz52 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (25224225381389 / 62500000000000000) ((√(23 : ℝ)) * x) := bmul (normalizedE52C_hz51 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz53 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (1 / 2) (31275224225381389 / 62500000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (normalizedE52C_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz54 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (13727269655396679 / 40000000000000000) (36200949034528061 / 100000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (normalizedE52C_hz50 _hx _hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz55 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (13727269655396679 / 40000000000000000) (181206538975691417 / 500000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (normalizedE52C_hz54 _hx _hc) (normalizedE52C_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz56 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (4278760031011243 / 12500000000000000) (342300802480900479 / 1000000000000000000) ((kdot ((68497037 / 125000000))) / (2 : ℝ)) := bdiv (normalizedE52C_hz22 _hx _hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz57 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (4278760031011243 / 12500000000000000) (342704390087002703 / 1000000000000000000) (((kdot ((68497037 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (normalizedE52C_hz56 _hx _hc) (normalizedE52C_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz58 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (176776695296636881 / 250000000000000000) (176848025788758493 / 250000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52C_hz53 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz59 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (4586769920300739 / 500000000000000000) (√x) := bsqrt (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz60 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (176776695296636881 / 250000000000000000) (14331312859912709 / 20000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (normalizedE52C_hz58 _hx _hc) (normalizedE52C_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz61 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (807175212204447 / 1000000000000000000) ((√(92 : ℝ)) * x) := bmul (normalizedE52C_hz3 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz62 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (176776695296636881 / 250000000000000000) (717372818207839897 / 1000000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52C_hz60 _hx _hc) (normalizedE52C_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz63 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (499999999999999999 / 500000000000000000) (253629592196833991 / 250000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz62 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz64 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (499999999999999999 / 500000000000000000) (253629592196833991 / 250000000000000000) (neb x (1/2+√23*x)) := by
    convert (normalizedE52C_hz63 _hx _hc) using 1 <;>
      norm_num [neb] <;> ring

theorem normalizedE52C_hz65 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (117012956971593439 / 200000000000000000) (585409591727879621 / 1000000000000000000) (√(((kdot ((68497037 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52C_hz57 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz66 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (117012956971593439 / 200000000000000000) (594583131568481099 / 1000000000000000000) ((√(((kdot ((68497037 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (normalizedE52C_hz65 _hx _hc) (normalizedE52C_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz67 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (117012956971593439 / 200000000000000000) (297695153390342773 / 500000000000000000) (((√(((kdot ((68497037 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52C_hz66 _hx _hc) (normalizedE52C_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz68 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (51712909600814639 / 62500000000000000) (168401809350944647 / 200000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((68497037 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz67 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz69 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (51712909600814639 / 62500000000000000) (168401809350944647 / 200000000000000000) (neb x (kdot (68497037 / 125000000)/2+√23*x)) := by
    convert (normalizedE52C_hz68 _hx _hc) using 1 <;>
      norm_num [neb] <;> ring

theorem normalizedE52C_hz70 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (12973344457548531 / 1000000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz71 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 1 (1012973344457548531 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (normalizedE52C_hz70 _hx _hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem normalizedE52C_hz72 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (43994751547921709 / 500000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (normalizedE52C_hz3 _hx _hc) (normalizedE52C_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz73 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 1 (1100962847553391949 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (normalizedE52C_hz71 _hx _hc) (normalizedE52C_hz72 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz74 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (176776695296636881 / 125000000000000000) (1556996590678909201 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz73 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz75 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (176776695296636881 / 125000000000000000) (1556996590678909201 / 1000000000000000000) (np1 x) := by
    convert (normalizedE52C_hz74 _hx _hc) using 1 <;>
      norm_num [np1] <;> ring

theorem normalizedE52C_hz76 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz3 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz77 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (185237340890323 / 200000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (normalizedE52C_hz76 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz78 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 1 (200185237340890323 / 200000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (normalizedE52C_hz77 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz79 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (176776695296636881 / 125000000000000000) (283104677634364033 / 200000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz78 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz80 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (275495636176222773 / 125000000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (normalizedE52C_hz79 _hx _hc) (normalizedE52C_hz75 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz81 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (275495636176222773 / 125000000000000000) (ntf x (np1 x)) := by
    convert (normalizedE52C_hz80 _hx _hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem normalizedE52C_hz82 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (176776695296636881 / 125000000000000000) (71359345341532179 / 50000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (normalizedE52C_hz70 _hx _hc) (normalizedE52C_hz4 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz83 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (176776695296636881 / 125000000000000000) (757588204963243499 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (normalizedE52C_hz82 _hx _hc) (normalizedE52C_hz72 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz84 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (2142783028305814153 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz83 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz85 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (2142783028305814153 / 1000000000000000000) (nz x) := by
    convert (normalizedE52C_hz84 _hx _hc) using 1 <;>
      norm_num [nz] <;> ring

theorem normalizedE52C_hz86 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (14645428923919337 / 25000000000000000) (301003769889756877 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52C_hz55 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz87 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (14645428923919337 / 12500000000000000) (301003769889756877 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz86 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz88 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (6890259834876489 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52C_hz70 _hx _hc) (normalizedE52C_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz89 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (2073994185817797 / 125000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52C_hz87 _hx _hc) (normalizedE52C_hz88 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz90 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (189902722368449 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (normalizedE52C_hz88 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz91 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (671274248356433 / 40000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (normalizedE52C_hz89 _hx _hc) (normalizedE52C_hz90 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz92 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (671274248356433 / 20000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz91 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz93 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (671274248356433 / 20000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (normalizedE52C_hz92 _hx _hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem normalizedE52C_hz94 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (999999999999999997 / 250000000000000000) (4857462115337069177 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (normalizedE52C_hz81 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz95 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (51096757082987 / 125000000000000000) (((ntf x (np1 x))^2) * x) := bmul (normalizedE52C_hz94 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz96 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (1999999999999999997 / 500000000000000000) (275495636176222773 / 62500000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz81 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz97 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (999999999999999997 / 125000000000000000) (9445237977131575037 / 1000000000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (normalizedE52C_hz96 _hx _hc) (normalizedE52C_hz85 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz98 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (199999999999999999 / 25000000000000000) (1197795928170965297 / 125000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (normalizedE52C_hz97 _hx _hc) (normalizedE52C_hz64 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz99 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (806392950043569 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (normalizedE52C_hz98 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz100 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (243033401341493 / 200000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (normalizedE52C_hz95 _hx _hc) (normalizedE52C_hz99 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz101 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (249999999999999999 / 250000000000000000) (51462376030345851 / 50000000000000000) ((neb x (1/2+√23*x))^2) := bsq (normalizedE52C_hz64 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz102 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (17272683894203263 / 500000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (normalizedE52C_hz93 _hx _hc) (normalizedE52C_hz101 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz103 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (35760534795113991 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (normalizedE52C_hz100 _hx _hc) (normalizedE52C_hz102 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz104 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (13727269655396679 / 20000000000000000) (181206538975691417 / 250000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz55 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz105 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (684601604961798877 / 1000000000000000000) (708979234816797699 / 1000000000000000000) ((neb x (kdot (68497037 / 125000000)/2+√23*x))^2) := bsq (normalizedE52C_hz69 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz106 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (2424238383385746723 / 1000000000000000000) ((np1 x)^2) := bsq (normalizedE52C_hz75 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz107 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B 0 (204008952569701 / 1000000000000000000) (((np1 x)^2) * x) := bmul (normalizedE52C_hz106 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz108 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (684601604961798877 / 1000000000000000000) (3545916218846837 / 5000000000000000) (((neb x (kdot (68497037 / 125000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (normalizedE52C_hz105 _hx _hc) (normalizedE52C_hz107 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz109 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (469885541891398311 / 1000000000000000000) (102806912882400913 / 200000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (68497037 / 125000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (normalizedE52C_hz104 _hx _hc) (normalizedE52C_hz108 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz110 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (469885541891398311 / 1000000000000000000) (137448774801779639 / 250000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (68497037 / 125000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (normalizedE52C_hz103 _hx _hc) (normalizedE52C_hz109 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz111 {x c : ℝ} (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) : B (469885541891398311 / 1000000000000000000) (137448774801779639 / 250000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (68497037 / 125000000)/2+√23*x)^2) (np1 x)) := by
    convert (normalizedE52C_hz110 _hx _hc) using 1 <;>
      norm_num [ne] <;> ring

theorem normalizedE52C {x c : ℝ}
    (_hx : B 0 (1/11883) x) (_hc : B (206684003 / 500000000) (68497037 / 125000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (68497037 / 125000000)/2+√23*x)^2) (np1 x) ≤ (137449 / 250000) :=
  (normalizedE52C_hz111 _hx _hc).2.trans (by norm_num)

end BstLean.Part281.TI
