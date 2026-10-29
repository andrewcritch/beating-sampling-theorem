import BstLean.Part264bNormalize
namespace BstLean.Part264b
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
theorem normalizedE52W_hz0 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (1 / 12227) x := _hx

theorem normalizedE52W_hz1 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (349910777 / 1000000000) (63424757 / 100000000) c := _hc

theorem normalizedE52W_hz2 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz3 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz4 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz5 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (277350535009621 / 250000000000000000) ((√(184 : ℝ)) * x) := bmul (normalizedE52W_hz2 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz6 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 1 (250277350535009621 / 250000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (normalizedE52W_hz5 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz7 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 1 (250277350535009621 / 250000000000000000) (nap x) := by
    convert (normalizedE52W_hz6 _hx _hc) using 1 <;>
      norm_num [nap] <;> ring

theorem normalizedE52W_hz8 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (1337796857 / 200000000000000000) (x^2) := bsq (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz9 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (1337796857 / 100000000000000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz8 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz10 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (99999998662203143 / 100000000000000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (normalizedE52W_hz9 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz11 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (249999998327753923 / 250000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (normalizedE52W_hz10 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz12 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (124861323896372151 / 125000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (normalizedE52W_hz11 _hx _hc) (normalizedE52W_hz5 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz13 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (124861323896372151 / 125000000000000000) 1 (nam x) := by
    convert (normalizedE52W_hz12 _hx _hc) using 1 <;>
      norm_num [nam] <;> ring

theorem normalizedE52W_hz14 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (613788099576286141 / 1000000000000000000) (38361756250805001 / 62500000000000000) (kdot ((349910777 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (693959221215680481 / 1000000000000000000)) (a := (303330117275023053 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (4337245132598003 / 6250000000000000)) (a := (606660233864246053 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52W_hz15 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (122437551860743729 / 1000000000000000000) (122437551860743729 / 1000000000000000000) (((349910777 / 1000000000) : ℝ)^2) := bsq (bpoint ((349910777 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz16 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (877562448139256271 / 1000000000000000000) (877562448139256271 / 1000000000000000000) ((1 : ℝ) - (((349910777 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (normalizedE52W_hz15 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz17 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (468391515758787061 / 500000000000000000) (936783031517574123 / 1000000000000000000) (√((1 : ℝ) - (((349910777 / 1000000000) : ℝ)^2))) := bsqrt (normalizedE52W_hz16 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz18 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (582397070588409 / 1953125000000000) (298187300141265409 / 1000000000000000000) ((√((1 : ℝ) - (((349910777 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (normalizedE52W_hz17 _hx _hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz19 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (107385535418045827 / 500000000000000000) (214771070988860557 / 1000000000000000000) (((349910777 / 1000000000) : ℝ) * (kdot ((349910777 / 1000000000)))) := bmul (bpoint ((349910777 / 1000000000) : ℝ)) (normalizedE52W_hz14 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz20 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (256479185488678531 / 500000000000000000) (256479185565062983 / 500000000000000000) (((√((1 : ℝ) - (((349910777 / 1000000000) : ℝ)^2))) / Real.pi) + (((349910777 / 1000000000) : ℝ) * (kdot ((349910777 / 1000000000))))) := badd (normalizedE52W_hz18 _hx _hc) (normalizedE52W_hz19 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz21 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (256479185488678531 / 500000000000000000) (256479185565062983 / 500000000000000000) (kappa ((349910777 / 1000000000))) := by rw [kappa_eq]; exact (normalizedE52W_hz20 _hx _hc)

theorem normalizedE52W_hz22 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (718690002529317443 / 1000000000000000000) (718690002529317447 / 1000000000000000000) (kdot ((63424757 / 100000000))) := by
    constructor
    · apply bkdot_lower (q := (14783753336603389 / 31250000000000000)) (a := (441880710717629819 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (473080106771308447 / 1000000000000000000)) (a := (441880710717629813 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52W_hz23 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (4022699800509049 / 10000000000000000) (4022699800509049 / 10000000000000000) (((63424757 / 100000000) : ℝ)^2) := bsq (bpoint ((63424757 / 100000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz24 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (5977300199490951 / 10000000000000000) (5977300199490951 / 10000000000000000) ((1 : ℝ) - (((63424757 / 100000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (normalizedE52W_hz23 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz25 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (6185040119250811 / 8000000000000000) (48320625931646961 / 62500000000000000) (√((1 : ℝ) - (((63424757 / 100000000) : ℝ)^2))) := bsqrt (normalizedE52W_hz24 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz26 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (246094927050113091 / 1000000000000000000) (61523731762528273 / 250000000000000000) ((√((1 : ℝ) - (((63424757 / 100000000) : ℝ)^2))) / Real.pi) := bdiv (normalizedE52W_hz25 _hx _hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz27 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (455827387687513441 / 1000000000000000000) (91165477537502689 / 200000000000000000) (((63424757 / 100000000) : ℝ) * (kdot ((63424757 / 100000000)))) := bmul (bpoint ((63424757 / 100000000) : ℝ)) (normalizedE52W_hz22 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz28 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (175480578684406633 / 250000000000000000) (701922314737626537 / 1000000000000000000) (((√((1 : ℝ) - (((63424757 / 100000000) : ℝ)^2))) / Real.pi) + (((63424757 / 100000000) : ℝ) * (kdot ((63424757 / 100000000))))) := badd (normalizedE52W_hz26 _hx _hc) (normalizedE52W_hz27 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz29 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (175480578684406633 / 250000000000000000) (701922314737626537 / 1000000000000000000) (kappa ((63424757 / 100000000))) := by rw [kappa_eq]; exact (normalizedE52W_hz28 _hx _hc)

theorem normalizedE52W_hz30 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (256479185488678531 / 500000000000000000) (701922314737626537 / 1000000000000000000) (kappa c) := bkappa (normalizedE52W_hz1 _hx _hc) (by norm_num) (by norm_num) (normalizedE52W_hz21 _hx _hc).1 (normalizedE52W_hz29 _hx _hc).2

theorem normalizedE52W_hz31 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (298077685262373463 / 1000000000000000000) (243520814511321469 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (normalizedE52W_hz30 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz32 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (298077685262373463 / 500000000000000000) (243520814511321469 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz31 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz33 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (1337796857 / 25000000000000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (normalizedE52W_hz8 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz34 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (298077658506436323 / 500000000000000000) (243520814511321469 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (normalizedE52W_hz32 _hx _hc) (normalizedE52W_hz33 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz35 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (772110948642015207 / 1000000000000000000) (493478281701759869 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (normalizedE52W_hz34 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz36 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz2 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz37 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (2218804280076967 / 1000000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (normalizedE52W_hz36 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz38 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (2405912951131057 / 3125000000000000) (493478281701759869 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (normalizedE52W_hz35 _hx _hc) (normalizedE52W_hz37 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz39 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (2405912951131057 / 3125000000000000) (493478281701759869 / 500000000000000000) (ndm x c) := by
    convert (normalizedE52W_hz38 _hx _hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem normalizedE52W_hz40 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 1 (100222003505318529 / 100000000000000000) ((nap x)^2) := bsq (normalizedE52W_hz7 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz41 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 2 (100222003505318529 / 50000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz40 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz42 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (592733913950223551 / 1000000000000000000) (974083258045285877 / 1000000000000000000) ((ndm x c)^2) := bsq (normalizedE52W_hz39 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz43 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (1025916741954714123 / 1000000000000000000) (1411706156156147029 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (normalizedE52W_hz41 _hx _hc) (normalizedE52W_hz42 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz44 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (997782413129904329 / 1000000000000000000) 1 ((nam x)^2) := bsq (normalizedE52W_hz13 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz45 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (997782413129904329 / 500000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz44 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz46 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (512958370977357061 / 1000000000000000000) (88427730934832627 / 125000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (normalizedE52W_hz43 _hx _hc) (normalizedE52W_hz45 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz47 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (512958370977357061 / 1000000000000000000) (88427730934832627 / 125000000000000000) (nc1 x c) := by
    convert (normalizedE52W_hz46 _hx _hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem normalizedE52W_hz48 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (335725241787022341 / 500000000000000000) (134290096714813459 / 200000000000000000) (kdot ((512958370977357061 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (567374159489870807 / 1000000000000000000)) (a := (516084373572130163 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (283687079744935403 / 500000000000000000)) (a := (129021093393023661 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52W_hz49 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (375070930639054363 / 500000000000000000) (93767732659763591 / 125000000000000000) (kdot ((88427730934832627 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (103488129704317857 / 250000000000000000)) (a := (196238123262078269 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (413952518817271427 / 1000000000000000000)) (a := (392476246524156537 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52W_hz50 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (335725241787022341 / 500000000000000000) (93767732659763591 / 125000000000000000) (kdot (nc1 x c)) := bkdot (normalizedE52W_hz47 _hx _hc) (normalizedE52W_hz48 _hx _hc).1 (normalizedE52W_hz49 _hx _hc).2

theorem normalizedE52W_hz51 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz52 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (9805822203551 / 25000000000000000) ((√(23 : ℝ)) * x) := bmul (normalizedE52W_hz51 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz53 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (1 / 2) (12509805822203551 / 25000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (normalizedE52W_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz54 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (335725241787022341 / 1000000000000000000) (93767732659763591 / 250000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (normalizedE52W_hz50 _hx _hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz55 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (335725241787022341 / 1000000000000000000) (93865790881799101 / 250000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (normalizedE52W_hz54 _hx _hc) (normalizedE52W_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz56 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (359345001264658721 / 1000000000000000000) (89836250316164681 / 250000000000000000) ((kdot ((63424757 / 100000000))) / (2 : ℝ)) := bdiv (normalizedE52W_hz22 _hx _hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz57 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (359345001264658721 / 1000000000000000000) (89934308538200191 / 250000000000000000) (((kdot ((63424757 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (normalizedE52W_hz56 _hx _hc) (normalizedE52W_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz58 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (176776695296636881 / 250000000000000000) (88423009668735091 / 125000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52W_hz53 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz59 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (4521786451305821 / 500000000000000000) (√x) := bsqrt (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz60 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (176776695296636881 / 250000000000000000) (71642765025249237 / 100000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (normalizedE52W_hz58 _hx _hc) (normalizedE52W_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz61 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (9805822203551 / 12500000000000000) ((√(92 : ℝ)) * x) := bmul (normalizedE52W_hz3 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz62 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (176776695296636881 / 250000000000000000) (14344242320575529 / 20000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52W_hz60 _hx _hc) (normalizedE52W_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz63 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (499999999999999999 / 500000000000000000) (126786387698275191 / 125000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz62 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz64 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (499999999999999999 / 500000000000000000) (126786387698275191 / 125000000000000000) (neb x (1/2+√23*x)) := by
    convert (normalizedE52W_hz63 _hx _hc) using 1 <;>
      norm_num [neb] <;> ring

theorem normalizedE52W_hz65 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (299726959608515497 / 500000000000000000) (299890494244482833 / 500000000000000000) (√(((kdot ((63424757 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52W_hz57 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz66 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (299726959608515497 / 500000000000000000) (152206140347894327 / 250000000000000000) ((√(((kdot ((63424757 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (normalizedE52W_hz65 _hx _hc) (normalizedE52W_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz67 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (299726959608515497 / 500000000000000000) (152402256791965347 / 250000000000000000) (((√(((kdot ((63424757 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52W_hz66 _hx _hc) (normalizedE52W_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz68 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (847755862574430941 / 1000000000000000000) (107764669245732267 / 125000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((63424757 / 100000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz67 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz69 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (847755862574430941 / 1000000000000000000) (107764669245732267 / 125000000000000000) (neb x (kdot (63424757 / 100000000)/2+√23*x)) := by
    convert (normalizedE52W_hz68 _hx _hc) using 1 <;>
      norm_num [neb] <;> ring

theorem normalizedE52W_hz70 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (6394771725591601 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz71 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 1 (506394771725591601 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (normalizedE52W_hz70 _hx _hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem normalizedE52W_hz72 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (5421431501215203 / 62500000000000000) ((√(92 : ℝ)) * (√x)) := bmul (normalizedE52W_hz3 _hx _hc) (normalizedE52W_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz73 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 1 (21990648949412529 / 20000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (normalizedE52W_hz71 _hx _hc) (normalizedE52W_hz72 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz74 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (176776695296636881 / 125000000000000000) (310994739896448527 / 200000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz73 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz75 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (176776695296636881 / 125000000000000000) (310994739896448527 / 200000000000000000) (np1 x) := by
    convert (normalizedE52W_hz74 _hx _hc) using 1 <;>
      norm_num [np1] <;> ring

theorem normalizedE52W_hz76 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz3 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz77 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (36005157795039 / 40000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (normalizedE52W_hz76 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz78 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 1 (40036005157795039 / 40000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (normalizedE52W_hz77 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz79 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (176776695296636881 / 125000000000000000) (1415486536934823237 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz78 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz80 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (2201044336904850169 / 1000000000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (normalizedE52W_hz79 _hx _hc) (normalizedE52W_hz75 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz81 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (2201044336904850169 / 1000000000000000000) (ntf x (np1 x)) := by
    convert (normalizedE52W_hz80 _hx _hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem normalizedE52W_hz82 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (176776695296636881 / 125000000000000000) (1427003105824278251 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (normalizedE52W_hz70 _hx _hc) (normalizedE52W_hz4 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz83 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (176776695296636881 / 125000000000000000) (1513746009843721499 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (normalizedE52W_hz82 _hx _hc) (normalizedE52W_hz72 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz84 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (2140760137109147587 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedE52W_hz4 _hx _hc) (normalizedE52W_hz83 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz85 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (2140760137109147587 / 1000000000000000000) (nz x) := by
    convert (normalizedE52W_hz84 _hx _hc) using 1 <;>
      norm_num [nz] <;> ring

theorem normalizedE52W_hz86 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (289709009950942991 / 500000000000000000) (24510019617362901 / 40000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52W_hz55 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz87 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (289709009950942991 / 250000000000000000) (24510019617362901 / 20000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz86 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz88 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (6787004613733641 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52W_hz70 _hx _hc) (normalizedE52W_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz89 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (8317480811287203 / 500000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52W_hz87 _hx _hc) (normalizedE52W_hz88 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz90 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (184253726507367 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (normalizedE52W_hz88 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz91 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (16819215349081773 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (normalizedE52W_hz89 _hx _hc) (normalizedE52W_hz90 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz92 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (16819215349081773 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz91 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz93 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (16819215349081773 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (normalizedE52W_hz92 _hx _hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem normalizedE52W_hz94 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (999999999999999997 / 250000000000000000) (605574521627613947 / 125000000000000000) ((ntf x (np1 x))^2) := bsq (normalizedE52W_hz81 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz95 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (7924423281297 / 20000000000000000) (((ntf x (np1 x))^2) * x) := bmul (normalizedE52W_hz94 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz96 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (1999999999999999997 / 500000000000000000) (2201044336904850169 / 500000000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz81 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz97 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (999999999999999997 / 125000000000000000) (1884763190582295953 / 200000000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (normalizedE52W_hz96 _hx _hc) (normalizedE52W_hz85 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz98 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (199999999999999999 / 25000000000000000) (4779246332012102139 / 500000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (normalizedE52W_hz97 _hx _hc) (normalizedE52W_hz64 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz99 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (781752896378851 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (normalizedE52W_hz98 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz100 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (1177974060443701 / 1000000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (normalizedE52W_hz95 _hx _hc) (normalizedE52W_hz99 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz101 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (249999999999999999 / 250000000000000000) (257196609689237547 / 250000000000000000) ((neb x (1/2+√23*x))^2) := bsq (normalizedE52W_hz64 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz102 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (6921352264667229 / 200000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (normalizedE52W_hz93 _hx _hc) (normalizedE52W_hz101 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz103 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (17892367691889923 / 500000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (normalizedE52W_hz100 _hx _hc) (normalizedE52W_hz102 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz104 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (335725241787022341 / 500000000000000000) (93865790881799101 / 125000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (normalizedE52W_hz55 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz105 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (718690002529317439 / 1000000000000000000) (74324633200909273 / 100000000000000000) ((neb x (kdot (63424757 / 100000000)/2+√23*x))^2) := bsq (normalizedE52W_hz69 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz106 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (1999999999999999997 / 1000000000000000000) (241794320608149183 / 100000000000000000) ((np1 x)^2) := bsq (normalizedE52W_hz75 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52W_hz107 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B 0 (98877206431729 / 500000000000000000) (((np1 x)^2) * x) := bmul (normalizedE52W_hz106 _hx _hc) (normalizedE52W_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz108 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (718690002529317439 / 1000000000000000000) (185861021605489047 / 250000000000000000) (((neb x (kdot (63424757 / 100000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (normalizedE52W_hz105 _hx _hc) (normalizedE52W_hz107 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz109 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (48256474973814159 / 100000000000000000) (34891983574196759 / 62500000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (63424757 / 100000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (normalizedE52W_hz104 _hx _hc) (normalizedE52W_hz108 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz110 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (48256474973814159 / 100000000000000000) (59405647257092799 / 100000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (63424757 / 100000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (normalizedE52W_hz103 _hx _hc) (normalizedE52W_hz109 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52W_hz111 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) : B (48256474973814159 / 100000000000000000) (59405647257092799 / 100000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (63424757 / 100000000)/2+√23*x)^2) (np1 x)) := by
    convert (normalizedE52W_hz110 _hx _hc) using 1 <;>
      norm_num [ne] <;> ring

theorem normalizedE52W {x c : ℝ}
    (_hx : B 0 (1/12227) x) (_hc : B (349910777 / 1000000000) (63424757 / 100000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (63424757 / 100000000)/2+√23*x)^2) (np1 x) ≤ (297031 / 500000) :=
  (normalizedE52W_hz111 _hx _hc).2.trans (by norm_num)

theorem normalizedE52C_hz0 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (1 / 12227) x := _hx

theorem normalizedE52C_hz1 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (414425269 / 1000000000) (546894481 / 1000000000) c := _hc

theorem normalizedE52C_hz2 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz3 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz4 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz5 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (277350535009621 / 250000000000000000) ((√(184 : ℝ)) * x) := bmul (normalizedE52C_hz2 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz6 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 1 (250277350535009621 / 250000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (normalizedE52C_hz5 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz7 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 1 (250277350535009621 / 250000000000000000) (nap x) := by
    convert (normalizedE52C_hz6 _hx _hc) using 1 <;>
      norm_num [nap] <;> ring

theorem normalizedE52C_hz8 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (1337796857 / 200000000000000000) (x^2) := bsq (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz9 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (1337796857 / 100000000000000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz8 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz10 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (99999998662203143 / 100000000000000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (normalizedE52C_hz9 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz11 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (249999998327753923 / 250000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (normalizedE52C_hz10 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz12 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (124861323896372151 / 125000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (normalizedE52C_hz11 _hx _hc) (normalizedE52C_hz5 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz13 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (124861323896372151 / 125000000000000000) 1 (nam x) := by
    convert (normalizedE52C_hz12 _hx _hc) using 1 <;>
      norm_num [nam] <;> ring

theorem normalizedE52C_hz14 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (636017378612459203 / 1000000000000000000) (636017378623205801 / 1000000000000000000) (kdot ((414425269 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (643429784385023149 / 1000000000000000000)) (a := (571742564692726661 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (160857446096255787 / 250000000000000000)) (a := (285871282337922973 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52C_hz15 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (171748303585722361 / 1000000000000000000) (171748303585722361 / 1000000000000000000) (((414425269 / 1000000000) : ℝ)^2) := bsq (bpoint ((414425269 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz16 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (828251696414277639 / 1000000000000000000) (828251696414277639 / 1000000000000000000) ((1 : ℝ) - (((414425269 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (normalizedE52C_hz15 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz17 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (455041672930699183 / 500000000000000000) (910083345861398367 / 1000000000000000000) (√((1 : ℝ) - (((414425269 / 1000000000) : ℝ)^2))) := bsqrt (normalizedE52C_hz16 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz18 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (144844263119452557 / 500000000000000000) (72422131559726279 / 250000000000000000) ((√((1 : ℝ) - (((414425269 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (normalizedE52C_hz17 _hx _hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz19 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (263581673220143251 / 1000000000000000000) (131790836612298457 / 500000000000000000) (((414425269 / 1000000000) : ℝ) * (kdot ((414425269 / 1000000000)))) := bmul (bpoint ((414425269 / 1000000000) : ℝ)) (normalizedE52C_hz14 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz20 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (110654039891809673 / 200000000000000000) (55327019946350203 / 100000000000000000) (((√((1 : ℝ) - (((414425269 / 1000000000) : ℝ)^2))) / Real.pi) + (((414425269 / 1000000000) : ℝ) * (kdot ((414425269 / 1000000000))))) := badd (normalizedE52C_hz18 _hx _hc) (normalizedE52C_hz19 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz21 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (110654039891809673 / 200000000000000000) (55327019946350203 / 100000000000000000) (kappa ((414425269 / 1000000000))) := by rw [kappa_eq]; exact (normalizedE52C_hz20 _hx _hc)

theorem normalizedE52C_hz22 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (342095058735396717 / 500000000000000000) (342095058735397837 / 500000000000000000) (kdot ((546894481 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (541214384759085639 / 1000000000000000000)) (a := (496073003442405469 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (270607192379542819 / 500000000000000000)) (a := (15502281357575061 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52C_hz23 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (299093573348259361 / 1000000000000000000) (299093573348259361 / 1000000000000000000) (((546894481 / 1000000000) : ℝ)^2) := bsq (bpoint ((546894481 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz24 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (700906426651740639 / 1000000000000000000) (700906426651740639 / 1000000000000000000) ((1 : ℝ) - (((546894481 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (normalizedE52C_hz23 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz25 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (837201544821640089 / 1000000000000000000) (83720154482164009 / 100000000000000000) (√((1 : ℝ) - (((546894481 / 1000000000) : ℝ)^2))) := bsqrt (normalizedE52C_hz24 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz26 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (266489528445069981 / 1000000000000000000) (133244764222534991 / 500000000000000000) ((√((1 : ℝ) - (((546894481 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (normalizedE52C_hz25 _hx _hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz27 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (374179799199518607 / 1000000000000000000) (374179799199519833 / 1000000000000000000) (((546894481 / 1000000000) : ℝ) * (kdot ((546894481 / 1000000000)))) := bmul (bpoint ((546894481 / 1000000000) : ℝ)) (normalizedE52C_hz22 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz28 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (160167331911147147 / 250000000000000000) (128133865528917963 / 200000000000000000) (((√((1 : ℝ) - (((546894481 / 1000000000) : ℝ)^2))) / Real.pi) + (((546894481 / 1000000000) : ℝ) * (kdot ((546894481 / 1000000000))))) := badd (normalizedE52C_hz26 _hx _hc) (normalizedE52C_hz27 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz29 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (160167331911147147 / 250000000000000000) (128133865528917963 / 200000000000000000) (kappa ((546894481 / 1000000000))) := by rw [kappa_eq]; exact (normalizedE52C_hz28 _hx _hc)

theorem normalizedE52C_hz30 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (110654039891809673 / 200000000000000000) (128133865528917963 / 200000000000000000) (kappa c) := bkappa (normalizedE52C_hz1 _hx _hc) (by norm_num) (by norm_num) (normalizedE52C_hz21 _hx _hc).1 (normalizedE52C_hz29 _hx _hc).2

theorem normalizedE52C_hz31 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (71866134471082037 / 200000000000000000) (89345960108190327 / 200000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (normalizedE52C_hz30 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz32 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (71866134471082037 / 100000000000000000) (89345960108190327 / 100000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz31 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz33 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (1337796857 / 25000000000000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (normalizedE52C_hz8 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz34 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (71866129119894609 / 100000000000000000) (89345960108190327 / 100000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (normalizedE52C_hz32 _hx _hc) (normalizedE52C_hz33 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz35 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (847738928679664969 / 1000000000000000000) (47261495984625351 / 50000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (normalizedE52C_hz34 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz36 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz2 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz37 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (2218804280076967 / 1000000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (normalizedE52C_hz36 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz38 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (422760062199794001 / 500000000000000000) (47261495984625351 / 50000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (normalizedE52C_hz35 _hx _hc) (normalizedE52C_hz37 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz39 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (422760062199794001 / 500000000000000000) (47261495984625351 / 50000000000000000) (ndm x c) := by
    convert (normalizedE52C_hz38 _hx _hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem normalizedE52C_hz40 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 1 (100222003505318529 / 100000000000000000) ((nap x)^2) := bsq (normalizedE52C_hz7 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz41 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 2 (100222003505318529 / 50000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz40 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz42 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (71490428076469477 / 100000000000000000) (893459601081903271 / 1000000000000000000) ((ndm x c)^2) := bsq (normalizedE52C_hz39 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz43 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (1106540398918096729 / 1000000000000000000) (128953578934167581 / 100000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (normalizedE52C_hz41 _hx _hc) (normalizedE52C_hz42 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz44 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (997782413129904329 / 1000000000000000000) 1 ((nam x)^2) := bsq (normalizedE52C_hz13 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz45 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (997782413129904329 / 500000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz44 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz46 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (138317549864762091 / 250000000000000000) (646200901305015897 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (normalizedE52C_hz43 _hx _hc) (normalizedE52C_hz45 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz47 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (138317549864762091 / 250000000000000000) (646200901305015897 / 1000000000000000000) (nc1 x c) := by
    convert (normalizedE52C_hz46 _hx _hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem normalizedE52C_hz48 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (686620293774526397 / 1000000000000000000) (686620293774527829 / 1000000000000000000) (kdot ((138317549864762091 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (134072271016241003 / 250000000000000000)) (a := (123063922857759433 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (536289084064964011 / 1000000000000000000)) (a := (123063922857758871 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52C_hz49 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (723643193040431187 / 1000000000000000000) (72364319304043119 / 100000000000000000) (kdot ((646200901305015897 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (463593078784631407 / 1000000000000000000)) (a := (434100257256857013 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (231796539392315703 / 500000000000000000)) (a := (434100257256857009 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem normalizedE52C_hz50 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (686620293774526397 / 1000000000000000000) (72364319304043119 / 100000000000000000) (kdot (nc1 x c)) := bkdot (normalizedE52C_hz47 _hx _hc) (normalizedE52C_hz48 _hx _hc).1 (normalizedE52C_hz49 _hx _hc).2

theorem normalizedE52C_hz51 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz52 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (9805822203551 / 25000000000000000) ((√(23 : ℝ)) * x) := bmul (normalizedE52C_hz51 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz53 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (1 / 2) (12509805822203551 / 25000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (normalizedE52C_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz54 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (171655073443631599 / 500000000000000000) (72364319304043119 / 200000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (normalizedE52C_hz50 _hx _hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz55 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (171655073443631599 / 500000000000000000) (72442765881671527 / 200000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (normalizedE52C_hz54 _hx _hc) (normalizedE52C_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz56 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (342095058735396717 / 1000000000000000000) (342095058735397837 / 1000000000000000000) ((kdot ((546894481 / 1000000000))) / (2 : ℝ)) := bdiv (normalizedE52C_hz22 _hx _hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz57 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (342095058735396717 / 1000000000000000000) (342487291623539877 / 1000000000000000000) (((kdot ((546894481 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (normalizedE52C_hz56 _hx _hc) (normalizedE52C_hz52 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz58 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (88423009668735091 / 125000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52C_hz53 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz59 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (4521786451305821 / 500000000000000000) (√x) := bsqrt (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz60 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (71642765025249237 / 100000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (normalizedE52C_hz58 _hx _hc) (normalizedE52C_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz61 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (9805822203551 / 12500000000000000) ((√(92 : ℝ)) * x) := bmul (normalizedE52C_hz3 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz62 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (14344242320575529 / 20000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52C_hz60 _hx _hc) (normalizedE52C_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz63 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (126786387698275191 / 125000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz62 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz64 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (126786387698275191 / 125000000000000000) (neb x (1/2+√23*x)) := by
    convert (normalizedE52C_hz63 _hx _hc) using 1 <;>
      norm_num [neb] <;> ring

theorem normalizedE52C_hz65 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (584888928545751083 / 1000000000000000000) (585224137936517343 / 1000000000000000000) (√(((kdot ((546894481 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52C_hz57 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz66 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (584888928545751083 / 1000000000000000000) (118853542167825797 / 200000000000000000) ((√(((kdot ((546894481 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (normalizedE52C_hz65 _hx _hc) (normalizedE52C_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz67 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (584888928545751083 / 1000000000000000000) (119010435323082613 / 200000000000000000) (((√(((kdot ((546894481 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52C_hz66 _hx _hc) (normalizedE52C_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz68 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (827157855231269281 / 1000000000000000000) (210382714622286859 / 250000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((546894481 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz67 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz69 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (827157855231269281 / 1000000000000000000) (210382714622286859 / 250000000000000000) (neb x (kdot (546894481 / 1000000000)/2+√23*x)) := by
    convert (normalizedE52C_hz68 _hx _hc) using 1 <;>
      norm_num [neb] <;> ring

theorem normalizedE52C_hz70 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (6394771725591601 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz71 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 1 (506394771725591601 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (normalizedE52C_hz70 _hx _hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem normalizedE52C_hz72 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (5421431501215203 / 62500000000000000) ((√(92 : ℝ)) * (√x)) := bmul (normalizedE52C_hz3 _hx _hc) (normalizedE52C_hz59 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz73 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 1 (21990648949412529 / 20000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (normalizedE52C_hz71 _hx _hc) (normalizedE52C_hz72 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz74 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (310994739896448527 / 200000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz73 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz75 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (310994739896448527 / 200000000000000000) (np1 x) := by
    convert (normalizedE52C_hz74 _hx _hc) using 1 <;>
      norm_num [np1] <;> ring

theorem normalizedE52C_hz76 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz3 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz77 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (36005157795039 / 40000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (normalizedE52C_hz76 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz78 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 1 (40036005157795039 / 40000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (normalizedE52C_hz77 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz79 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1415486536934823237 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz78 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz80 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2201044336904850169 / 1000000000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (normalizedE52C_hz79 _hx _hc) (normalizedE52C_hz75 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz81 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2201044336904850169 / 1000000000000000000) (ntf x (np1 x)) := by
    convert (normalizedE52C_hz80 _hx _hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem normalizedE52C_hz82 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1427003105824278251 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (normalizedE52C_hz70 _hx _hc) (normalizedE52C_hz4 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz83 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1513746009843721499 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (normalizedE52C_hz82 _hx _hc) (normalizedE52C_hz72 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz84 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2140760137109147587 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedE52C_hz4 _hx _hc) (normalizedE52C_hz83 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz85 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2140760137109147587 / 1000000000000000000) (nz x) := by
    convert (normalizedE52C_hz84 _hx _hc) using 1 <;>
      norm_num [nz] <;> ring

theorem normalizedE52C_hz86 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (585926741911702813 / 1000000000000000000) (300921015138672907 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedE52C_hz55 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz87 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (585926741911702813 / 500000000000000000) (300921015138672907 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz86 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz88 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (6787004613733641 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (normalizedE52C_hz70 _hx _hc) (normalizedE52C_hz61 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz89 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (16338818544924671 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (normalizedE52C_hz87 _hx _hc) (normalizedE52C_hz88 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz90 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (184253726507367 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (normalizedE52C_hz88 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz91 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (8261536135716019 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (normalizedE52C_hz89 _hx _hc) (normalizedE52C_hz90 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz92 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (8261536135716019 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz91 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz93 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (8261536135716019 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (normalizedE52C_hz92 _hx _hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem normalizedE52C_hz94 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (605574521627613947 / 125000000000000000) ((ntf x (np1 x))^2) := bsq (normalizedE52C_hz81 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz95 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (7924423281297 / 20000000000000000) (((ntf x (np1 x))^2) * x) := bmul (normalizedE52C_hz94 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz96 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (2201044336904850169 / 500000000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz81 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz97 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (1884763190582295953 / 200000000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (normalizedE52C_hz96 _hx _hc) (normalizedE52C_hz85 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz98 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (4779246332012102139 / 500000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (normalizedE52C_hz97 _hx _hc) (normalizedE52C_hz64 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz99 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (781752896378851 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (normalizedE52C_hz98 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz100 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (1177974060443701 / 1000000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (normalizedE52C_hz95 _hx _hc) (normalizedE52C_hz99 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz101 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (257196609689237547 / 250000000000000000) ((neb x (1/2+√23*x))^2) := bsq (normalizedE52C_hz64 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz102 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (33997425358900557 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (normalizedE52C_hz93 _hx _hc) (normalizedE52C_hz101 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz103 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (17587699709672129 / 500000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (normalizedE52C_hz100 _hx _hc) (normalizedE52C_hz102 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz104 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (171655073443631599 / 250000000000000000) (72442765881671527 / 100000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (normalizedE52C_hz55 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz105 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (684190117470793429 / 1000000000000000000) (44260886611842593 / 62500000000000000) ((neb x (kdot (546894481 / 1000000000)/2+√23*x))^2) := bsq (normalizedE52C_hz69 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz106 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (241794320608149183 / 100000000000000000) ((np1 x)^2) := bsq (normalizedE52C_hz75 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedE52C_hz107 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B 0 (98877206431729 / 500000000000000000) (((np1 x)^2) * x) := bmul (normalizedE52C_hz106 _hx _hc) (normalizedE52C_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz108 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (684190117470793429 / 1000000000000000000) (354185970101172473 / 500000000000000000) (((neb x (kdot (546894481 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (normalizedE52C_hz105 _hx _hc) (normalizedE52C_hz107 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz109 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (469778819455423909 / 1000000000000000000) (4009095517283117 / 7812500000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (546894481 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (normalizedE52C_hz104 _hx _hc) (normalizedE52C_hz108 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz110 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (469778819455423909 / 1000000000000000000) (274169812815791617 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (546894481 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (normalizedE52C_hz103 _hx _hc) (normalizedE52C_hz109 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedE52C_hz111 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) : B (469778819455423909 / 1000000000000000000) (274169812815791617 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (546894481 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (normalizedE52C_hz110 _hx _hc) using 1 <;>
      norm_num [ne] <;> ring

theorem normalizedE52C {x c : ℝ}
    (_hx : B 0 (1/12227) x) (_hc : B (414425269 / 1000000000) (546894481 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (546894481 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (109669 / 200000) :=
  (normalizedE52C_hz111 _hx _hc).2.trans (by norm_num)

end BstLean.Part264b
