import BstLean.Part281Normalize
namespace BstLean.Part281.TI
open BstLean.Part264b
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
theorem normalizedO_hz0 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (1 / 11883) x := hx

theorem normalizedO_hz1 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 1 c := hc

theorem normalizedO_hz2 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz3 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz4 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz5 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (25224225381389 / 62500000000000000) ((√(23 : ℝ)) * x) := bmul (normalizedO_hz4 hx hc) (normalizedO_hz0 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz6 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (1 / 2) (31275224225381389 / 62500000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (normalizedO_hz5 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz7 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (4586769920300739 / 500000000000000000) (√x) := bsqrt (normalizedO_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz8 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (43994751547921709 / 500000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (normalizedO_hz3 hx hc) (normalizedO_hz7 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz9 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 1 (543994751547921709 / 500000000000000000) ((1 : ℝ) + ((√(92 : ℝ)) * (√x))) := badd (bpoint (1 : ℝ)) (normalizedO_hz8 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz10 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (176776695296636881 / 125000000000000000) (307729902199541249 / 200000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + ((√(92 : ℝ)) * (√x)))) := bmul (normalizedO_hz2 hx hc) (normalizedO_hz9 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz11 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (1732050807568877293 / 1000000000000000000) (866025403784438647 / 500000000000000000) (√(3 : ℝ)) := bsqrt (bpoint (3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz12 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (1415464231774289547 / 125000000000000000) (5661856927097158189 / 500000000000000000) ((√(3 : ℝ)) + (√(92 : ℝ))) := badd (normalizedO_hz11 hx hc) (normalizedO_hz3 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz13 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (476466963485413 / 500000000000000000) (((√(3 : ℝ)) + (√(92 : ℝ))) * x) := bmul (normalizedO_hz12 hx hc) (normalizedO_hz0 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz14 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 1 (500476466963485413 / 500000000000000000) ((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (normalizedO_hz13 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz15 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (176776695296636881 / 250000000000000000) (176848025788758493 / 250000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (normalizedO_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz16 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (426776695296636881 / 250000000000000000) (854172518541002399 / 500000000000000000) (((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) := badd (normalizedO_hz14 hx hc) (normalizedO_hz15 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz17 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (807175212204447 / 1000000000000000000) ((√(92 : ℝ)) * x) := bmul (normalizedO_hz3 hx hc) (normalizedO_hz0 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz18 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (426776695296636881 / 250000000000000000) (341830442458841849 / 200000000000000000) ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x)) := badd (normalizedO_hz16 hx hc) (normalizedO_hz17 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz19 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (1207106781186547523 / 500000000000000000) (2417106238786450077 / 1000000000000000000) ((√(2 : ℝ)) * ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x))) := bmul (normalizedO_hz2 hx hc) (normalizedO_hz18 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz20 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz21 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (3836665218650175631 / 200000000000000000) (19183326093250878171 / 1000000000000000000) ((√(184 : ℝ)) * (√(2 : ℝ))) := bmul (normalizedO_hz20 hx hc) (normalizedO_hz2 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz22 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 1 (1000807175212204447 / 1000000000000000000) ((1 : ℝ) + ((√(92 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (normalizedO_hz17 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz23 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (3836665218650175631 / 200000000000000000) (9599405199280492527 / 500000000000000000) (((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) := bmul (normalizedO_hz21 hx hc) (normalizedO_hz22 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz24 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (201956686006911 / 125000000000000000) ((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) := bmul (normalizedO_hz23 hx hc) (normalizedO_hz0 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz25 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (7410630820641 / 500000000000000000) (((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) * (√x)) := bmul (normalizedO_hz24 hx hc) (normalizedO_hz7 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz26 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (4586769920300739 / 250000000000000000) ((2 : ℝ) * (√x)) := bmul (bpoint (2 : ℝ)) (normalizedO_hz7 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz27 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (176776695296636881 / 250000000000000000) (708199278367238419 / 1000000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (normalizedO_hz15 hx hc) (normalizedO_hz17 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz28 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (499999999999999999 / 1000000000000000000) (501546217879877251 / 1000000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (normalizedO_hz27 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem normalizedO_hz29 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (9201908423248087 / 1000000000000000000) (((2 : ℝ) * (√x)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (normalizedO_hz26 hx hc) (normalizedO_hz28 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz30 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (9216729684889369 / 1000000000000000000) ((((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) * (√x)) + (((2 : ℝ) * (√x)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2))) := badd (normalizedO_hz25 hx hc) (normalizedO_hz29 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz31 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B (1707106781186547521 / 500000000000000000) (743815866467655279 / 200000000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + ((√(92 : ℝ)) * (√x)))) * ((√(2 : ℝ)) * ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x)))) := bmul (normalizedO_hz10 hx hc) (normalizedO_hz19 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz32 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (4284718610352591 / 125000000000000000) ((((√(2 : ℝ)) * ((1 : ℝ) + ((√(92 : ℝ)) * (√x)))) * ((√(2 : ℝ)) * ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x)))) * ((((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) * (√x)) + (((2 : ℝ) * (√x)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)))) := bmul (normalizedO_hz31 hx hc) (normalizedO_hz30 hx hc) (by norm_num) (by norm_num)

theorem normalizedO_hz33 {x c : ℝ} (hx : B 0 (1/11883) x) (hc : B 0 1 c) : B 0 (4284718610352591 / 125000000000000000) (no x) := by
    convert (normalizedO_hz32 hx hc) using 1 <;>
      norm_num [no] <;> ring

theorem normalizedO {x : ℝ} (hx : B 0 (1/11883) x) : no x ≤ ((17139/500000) : ℝ) := by
  have hc : B 0 1 (0 : ℝ) := by constructor <;> norm_num
  exact (normalizedO_hz33 hx hc).2.trans (by norm_num)

end BstLean.Part281.TI
