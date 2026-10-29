import BstLean.Part264bNormalize
namespace BstLean.Part264b
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
theorem normalizedO_hz0 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (1 / 12227) x := _hx

theorem normalizedO_hz1 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 1 c := _hc

theorem normalizedO_hz2 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz3 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz4 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz5 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (9805822203551 / 25000000000000000) ((√(23 : ℝ)) * x) := bmul (normalizedO_hz4 _hx _hc) (normalizedO_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz6 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (1 / 2) (12509805822203551 / 25000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (normalizedO_hz5 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz7 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (4521786451305821 / 500000000000000000) (√x) := bsqrt (normalizedO_hz0 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz8 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (5421431501215203 / 62500000000000000) ((√(92 : ℝ)) * (√x)) := bmul (normalizedO_hz3 _hx _hc) (normalizedO_hz7 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz9 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 1 (67921431501215203 / 62500000000000000) ((1 : ℝ) + ((√(92 : ℝ)) * (√x))) := badd (bpoint (1 : ℝ)) (normalizedO_hz8 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz10 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (176776695296636881 / 125000000000000000) (1536886553677019351 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedO_hz2 _hx _hc) (normalizedO_hz9 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz11 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (1732050807568877293 / 1000000000000000000) (866025403784438647 / 500000000000000000) (√(3 : ℝ)) := bsqrt (bpoint (3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz12 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (1415464231774289547 / 125000000000000000) (5661856927097158189 / 500000000000000000) ((√(3 : ℝ)) + (√(92 : ℝ))) := badd (normalizedO_hz11 _hx _hc) (normalizedO_hz3 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz13 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (57882728051619 / 62500000000000000) (((√(3 : ℝ)) + (√(92 : ℝ))) * x) := bmul (normalizedO_hz12 _hx _hc) (normalizedO_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz14 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 1 (62557882728051619 / 62500000000000000) ((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (normalizedO_hz13 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz15 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (176776695296636881 / 250000000000000000) (88423009668735091 / 125000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedO_hz6 _hx _hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz16 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (426776695296636881 / 250000000000000000) (213538775124838329 / 125000000000000000) (((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) := badd (normalizedO_hz14 _hx _hc) (normalizedO_hz15 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz17 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (9805822203551 / 12500000000000000) ((√(92 : ℝ)) * x) := bmul (normalizedO_hz3 _hx _hc) (normalizedO_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz18 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (426776695296636881 / 250000000000000000) (213636833346873839 / 125000000000000000) ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x)) := badd (normalizedO_hz16 _hx _hc) (normalizedO_hz17 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz19 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (1207106781186547523 / 500000000000000000) (1208512428566358713 / 500000000000000000) ((√(2 : ℝ)) * ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x))) := bmul (normalizedO_hz2 _hx _hc) (normalizedO_hz18 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz20 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz21 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (3836665218650175631 / 200000000000000000) (19183326093250878171 / 1000000000000000000) ((√(184 : ℝ)) * (√(2 : ℝ))) := bmul (normalizedO_hz20 _hx _hc) (normalizedO_hz2 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz22 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 1 (12509805822203551 / 12500000000000000) ((1 : ℝ) + ((√(92 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (normalizedO_hz17 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz23 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (3836665218650175631 / 200000000000000000) (19198374756046330869 / 1000000000000000000) (((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) := bmul (normalizedO_hz21 _hx _hc) (normalizedO_hz22 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz24 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (1570162325676481 / 1000000000000000000) ((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) := bmul (normalizedO_hz23 _hx _hc) (normalizedO_hz0 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz25 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (1419987746119 / 100000000000000000) (((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) * (√x)) := bmul (normalizedO_hz24 _hx _hc) (normalizedO_hz7 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz26 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (4521786451305821 / 250000000000000000) ((2 : ℝ) * (√x)) := bmul (bpoint (2 : ℝ)) (normalizedO_hz7 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz27 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (176776695296636881 / 250000000000000000) (88521067890770601 / 125000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (normalizedO_hz15 _hx _hc) (normalizedO_hz17 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz28 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (499999999999999999 / 1000000000000000000) (250751342736717373 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (normalizedO_hz27 _hx _hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz29 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (1133844024233631 / 125000000000000000) (((2 : ℝ) * (√x)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (normalizedO_hz26 _hx _hc) (normalizedO_hz28 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz30 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (4542476035665119 / 500000000000000000) ((((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) * (√x)) + (((2 : ℝ) * (√x)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2))) := badd (normalizedO_hz25 _hx _hc) (normalizedO_hz29 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz31 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B (1707106781186547521 / 500000000000000000) (3714693002830392149 / 1000000000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + ((√(92 : ℝ)) * (√x)))) * ((√(2 : ℝ)) * ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x)))) := bmul (normalizedO_hz10 _hx _hc) (normalizedO_hz19 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz32 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (33747807890419913 / 1000000000000000000) ((((√(2 : ℝ)) * ((1 : ℝ) + ((√(92 : ℝ)) * (√x)))) * ((√(2 : ℝ)) * ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x)))) * ((((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) * (√x)) + (((2 : ℝ) * (√x)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)))) := bmul (normalizedO_hz31 _hx _hc) (normalizedO_hz30 _hx _hc) (by norm_num) (by norm_num)

theorem normalizedO_hz33 {x c : ℝ} (_hx : B 0 (1/12227) x) (_hc : B 0 1 c) : B 0 (33747807890419913 / 1000000000000000000) (no x) := by
    convert (normalizedO_hz32 _hx _hc) using 1 <;>
      norm_num [no] <;> ring

theorem normalizedO {x : ℝ} (_hx : B 0 (1/12227) x) : no x ≤ (33751/10^6 : ℝ) := by
  have _hc : B 0 1 (0 : ℝ) := by constructor <;> norm_num
  exact (normalizedO_hz33 _hx _hc).2.trans (by norm_num)

end BstLean.Part264b
