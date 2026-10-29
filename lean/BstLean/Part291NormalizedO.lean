import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255 BstLean.Part264b
theorem lowNormalizedO_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (1 / 8000) x := hx

theorem lowNormalizedO_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowNormalizedO_hz3 hx hc) (lowNormalizedO_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowNormalizedO_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowNormalizedO_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowNormalizedO_hz2 hx hc) (lowNormalizedO_hz6 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 1 (1107238052947636089 / 1000000000000000000) ((1 : ℝ) + ((√(92 : ℝ)) * (√x))) := badd (bpoint (1 : ℝ)) (lowNormalizedO_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (176776695296636881 / 125000000000000000) (1565871071254126069 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + ((√(92 : ℝ)) * (√x)))) := bmul (lowNormalizedO_hz1 hx hc) (lowNormalizedO_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (1732050807568877293 / 1000000000000000000) (866025403784438647 / 500000000000000000) (√(3 : ℝ)) := bsqrt (bpoint (3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (1415464231774289547 / 125000000000000000) (5661856927097158189 / 500000000000000000) ((√(3 : ℝ)) + (√(92 : ℝ))) := badd (lowNormalizedO_hz10 hx hc) (lowNormalizedO_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (141546423177429 / 100000000000000000) (((√(3 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowNormalizedO_hz11 hx hc) (lowNormalizedO_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 1 (100141546423177429 / 100000000000000000) ((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowNormalizedO_hz12 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowNormalizedO_hz5 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (426776695296636881 / 250000000000000000) (427236503515032279 / 250000000000000000) (((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) := badd (lowNormalizedO_hz13 hx hc) (lowNormalizedO_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowNormalizedO_hz2 hx hc) (lowNormalizedO_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (426776695296636881 / 250000000000000000) (106884060746309831 / 62500000000000000) ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x)) := badd (lowNormalizedO_hz15 hx hc) (lowNormalizedO_hz16 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (1207106781186547523 / 500000000000000000) (1209255106471528947 / 500000000000000000) ((√(2 : ℝ)) * ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x))) := bmul (lowNormalizedO_hz1 hx hc) (lowNormalizedO_hz17 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (3836665218650175631 / 200000000000000000) (19183326093250878171 / 1000000000000000000) ((√(184 : ℝ)) * (√(2 : ℝ))) := bmul (lowNormalizedO_hz19 hx hc) (lowNormalizedO_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 1 (50059947894041409 / 50000000000000000) ((1 : ℝ) + ((√(92 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowNormalizedO_hz16 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (3836665218650175631 / 200000000000000000) (9603163046625439087 / 500000000000000000) (((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) := bmul (lowNormalizedO_hz20 hx hc) (lowNormalizedO_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (60019769041409 / 25000000000000000) ((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) := bmul (lowNormalizedO_hz22 hx hc) (lowNormalizedO_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (13420828357043 / 500000000000000000) (((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) * (√x)) := bmul (lowNormalizedO_hz23 hx hc) (lowNormalizedO_hz6 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (11180339887498949 / 500000000000000000) ((2 : ℝ) * (√x)) := bmul (bpoint (2 : ℝ)) (lowNormalizedO_hz6 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowNormalizedO_hz14 hx hc) (lowNormalizedO_hz16 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowNormalizedO_hz26 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (5615856943438431 / 500000000000000000) (((2 : ℝ) * (√x)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (lowNormalizedO_hz25 hx hc) (lowNormalizedO_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (2814638885897737 / 250000000000000000) ((((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) * (√x)) + (((2 : ℝ) * (√x)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2))) := badd (lowNormalizedO_hz24 hx hc) (lowNormalizedO_hz28 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B (1707106781186547521 / 500000000000000000) (189353758899009531 / 50000000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + ((√(92 : ℝ)) * (√x)))) * ((√(2 : ℝ)) * ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x)))) := bmul (lowNormalizedO_hz9 hx hc) (lowNormalizedO_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (5329624529880569 / 125000000000000000) ((((√(2 : ℝ)) * ((1 : ℝ) + ((√(92 : ℝ)) * (√x)))) * ((√(2 : ℝ)) * ((((1 : ℝ) + (((√(3 : ℝ)) + (√(92 : ℝ))) * x)) + (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)))) + ((√(92 : ℝ)) * x)))) * ((((((√(184 : ℝ)) * (√(2 : ℝ))) * ((1 : ℝ) + ((√(92 : ℝ)) * x))) * x) * (√x)) + (((2 : ℝ) * (√x)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)))) := bmul (lowNormalizedO_hz30 hx hc) (lowNormalizedO_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowNormalizedO_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0 1 c) : B 0 (5329624529880569 / 125000000000000000) (no x) := by
    convert (lowNormalizedO_hz31 hx hc) using 1 <;>
      norm_num [no] <;> ring

theorem lowNormalizedO {x : ℝ} (hx : B 0 (1/8000) x) : no x ≤ (42636997 / 1000000000) := by
  have hc : B 0 1 (0 : ℝ) := by constructor <;> norm_num
  exact (lowNormalizedO_hz32 hx hc).2.trans (by norm_num)

end BstLean.BlueprintLow
