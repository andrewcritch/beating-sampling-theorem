import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part199 BstLean.Part255 BstLean.Part264b
theorem lowGeometry96W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (127 / 250) (1017 / 2000) θ := hc

theorem lowGeometry96W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry96W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (983 / 2000) (123 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry96W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (124841 / 500000) (125091 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry96W_hz0 hx hc) (lowGeometry96W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (125091 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry96W_hz3 hx hc) (lowGeometry96W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (5592204395406163 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry96W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (16776613186218489 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry96W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (127 / 125) (1017 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry96W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry96W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry96W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1017 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry96W_hz7 hx hc) (lowGeometry96W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (29489113186218489 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry96W_hz6 hx hc) (lowGeometry96W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (29489113186218489 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry96W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry96W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (508 / 25) (1017 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry96W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1017 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry96W_hz13 hx hc) (lowGeometry96W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (30124738186218489 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry96W_hz12 hx hc) (lowGeometry96W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (30124738186218489 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry96W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry96W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1017 / 16000000) (θ * x) := bmul (lowGeometry96W_hz0 hx hc) (lowGeometry96W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (64661749745677 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry96W_hz17 hx hc) (lowGeometry96W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1137204904541631 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry96W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (3411614713624893 / 50000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry96W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (3411614713624893 / 50000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry96W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry96W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (508 / 125) (1017 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry96W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry96W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1819264906493829 / 40000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry96W_hz22 hx hc) (lowGeometry96W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry96W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry96W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry96W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry96W_hz26 hx hc) (lowGeometry96W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry96W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (11952454481193393 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry96W_hz24 hx hc) (lowGeometry96W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (53411614713624893 / 50000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry96W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (228224046905336893 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry96W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (983 / 2000) (561431155387128757 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry96W_hz2 hx hc) (lowGeometry96W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (983 / 2000) (609240973311902329 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry96W_hz33 hx hc) (lowGeometry96W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (983 / 2000) (609240973311902329 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry96W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry96W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (46588385286375107 / 50000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry96W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (27130970544896657 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry96W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (426715904730134621 / 1000000000000000000) (123 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry96W_hz2 hx hc) (lowGeometry96W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (378906086805361049 / 1000000000000000000) (123 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry96W_hz38 hx hc) (lowGeometry96W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (378906086805361049 / 1000000000000000000) (123 / 250) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry96W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry96W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (127 / 250) (1017 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (169079179 / 500000000) (6907153 / 10000000) ∧ radiusMinus n θ lowWideWindow ≤ (117956453 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry96W_hz12 hx hc).2
  have hrp := (lowGeometry96W_hz16 hx hc).2
  have hbn := (lowGeometry96W_hz21 hx hc).2
  have hlo := (lowGeometry96W_hz40 hx hc).1
  have hhi := (lowGeometry96W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry96C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (127 / 250) (1017 / 2000) θ := hc

theorem lowGeometry96C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry96C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (983 / 2000) (123 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry96C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (124841 / 500000) (125091 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry96C_hz0 hx hc) (lowGeometry96C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (125091 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry96C_hz3 hx hc) (lowGeometry96C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (5592204395406163 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry96C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (32211097317539499 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry96C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (127 / 125) (1017 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry96C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry96C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry96C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (317761645931349 / 10000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry96C_hz7 hx hc) (lowGeometry96C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (63987261910674399 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry96C_hz6 hx hc) (lowGeometry96C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (63987261910674399 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry96C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry96C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (99187 / 12500) (794277 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry96C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (794277 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry96C_hz13 hx hc) (lowGeometry96C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (64980108160674399 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry96C_hz12 hx hc) (lowGeometry96C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (64980108160674399 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry96C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry96C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1017 / 16000000) (θ * x) := bmul (lowGeometry96C_hz0 hx hc) (lowGeometry96C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (64661749745677 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry96C_hz17 hx hc) (lowGeometry96C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (1137204904541631 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry96C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (32751501250798973 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry96C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (32751501250798973 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry96C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry96C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (41529 / 25000) (332559 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry96C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry96C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (3718122652646763 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry96C_hz22 hx hc) (lowGeometry96C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry96C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry96C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry96C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry96C_hz26 hx hc) (lowGeometry96C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry96C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 0 (4795068637065501 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry96C_hz24 hx hc) (lowGeometry96C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (1032751501250798973 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry96C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B 1 (1066575663335779033 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry96C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (983 / 2000) (104951045272240657 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry96C_hz2 hx hc) (lowGeometry96C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (983 / 2000) (543935500909465289 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry96C_hz33 hx hc) (lowGeometry96C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (983 / 2000) (543935500909465289 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry96C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry96C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (967248498749201027 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry96C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (46778482916629157 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry96C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (459832487070464613 / 1000000000000000000) (123 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry96C_hz2 hx hc) (lowGeometry96C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (440652212522202609 / 1000000000000000000) (123 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry96C_hz38 hx hc) (lowGeometry96C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry96C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (127 / 250) (1017 / 2000) θ) : B (440652212522202609 / 1000000000000000000) (123 / 250) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry96C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry96C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (127 / 250) (1017 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (206882837 / 500000000) (145279941 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31993631 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry96C_hz12 hx hc).2
  have hrp := (lowGeometry96C_hz16 hx hc).2
  have hbn := (lowGeometry96C_hz21 hx hc).2
  have hlo := (lowGeometry96C_hz40 hx hc).1
  have hhi := (lowGeometry96C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry97W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (1017 / 2000) (509 / 1000) θ := hc

theorem lowGeometry97W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry97W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (491 / 1000) (983 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry97W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (499347 / 2000000) (500347 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry97W_hz0 hx hc) (lowGeometry97W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (500347 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry97W_hz3 hx hc) (lowGeometry97W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (5592109396283303 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry97W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (16776328188849909 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry97W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (1017 / 1000) (509 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry97W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry97W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry97W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (509 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry97W_hz7 hx hc) (lowGeometry97W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (29501328188849909 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry97W_hz6 hx hc) (lowGeometry97W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (29501328188849909 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry97W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry97W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (1017 / 50) (509 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry97W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (509 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry97W_hz13 hx hc) (lowGeometry97W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (30137578188849909 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry97W_hz12 hx hc) (lowGeometry97W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (30137578188849909 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry97W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry97W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (509 / 8000000) (θ * x) := bmul (lowGeometry97W_hz0 hx hc) (lowGeometry97W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (129582484725051 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry97W_hz17 hx hc) (lowGeometry97W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (5691715135287671 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry97W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (17075145405863013 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry97W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (17075145405863013 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry97W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry97W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (1017 / 250) (509 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry97W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry97W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (45526344021895721 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry97W_hz22 hx hc) (lowGeometry97W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry97W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry97W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry97W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry97W_hz26 hx hc) (lowGeometry97W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry97W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (1495525892558367 / 31250000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry97W_hz24 hx hc) (lowGeometry97W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (267075145405863013 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry97W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (1141266132697005941 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry97W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (491 / 1000) (560932304220578421 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry97W_hz2 hx hc) (lowGeometry97W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (491 / 1000) (121757826556489233 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry97W_hz33 hx hc) (lowGeometry97W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (491 / 1000) (121757826556489233 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry97W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry97W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (232924854594136987 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry97W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (217015951550799433 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry97W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (213109664422885043 / 500000000000000000) (983 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry97W_hz2 hx hc) (lowGeometry97W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (189181250141951171 / 500000000000000000) (983 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry97W_hz38 hx hc) (lowGeometry97W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (189181250141951171 / 500000000000000000) (983 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry97W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry97W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1017 / 2000) (509 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (42207219 / 125000000) (69024127 / 100000000) ∧ radiusMinus n θ lowWideWindow ≤ (118005313 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry97W_hz12 hx hc).2
  have hrp := (lowGeometry97W_hz16 hx hc).2
  have hbn := (lowGeometry97W_hz21 hx hc).2
  have hlo := (lowGeometry97W_hz40 hx hc).1
  have hhi := (lowGeometry97W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry97C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (1017 / 2000) (509 / 1000) θ := hc

theorem lowGeometry97C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry97C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (491 / 1000) (983 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry97C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (499347 / 2000000) (500347 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry97C_hz0 hx hc) (lowGeometry97C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (500347 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry97C_hz3 hx hc) (lowGeometry97C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (5592109396283303 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry97C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (16105275061295913 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry97C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (1017 / 1000) (509 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry97C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry97C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry97C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (7951852398183709 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry97C_hz7 hx hc) (lowGeometry97C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (32008979857663331 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry97C_hz6 hx hc) (lowGeometry97C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (32008979857663331 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry97C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry97C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (794277 / 100000) (397529 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry97C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (397529 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry97C_hz13 hx hc) (lowGeometry97C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (32505891107663331 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry97C_hz12 hx hc) (lowGeometry97C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (32505891107663331 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry97C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry97C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (509 / 8000000) (θ * x) := bmul (lowGeometry97C_hz0 hx hc) (lowGeometry97C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (129582484725051 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry97C_hz17 hx hc) (lowGeometry97C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (5691715135287671 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry97C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (6556855835851397 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry97C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (6556855835851397 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry97C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry97C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (332559 / 200000) (166443 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry97C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry97C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (4652223279737469 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry97C_hz22 hx hc) (lowGeometry97C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry97C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry97C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry97C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry97C_hz26 hx hc) (lowGeometry97C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry97C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 0 (19199134208584779 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry97C_hz24 hx hc) (lowGeometry97C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (206556855835851397 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry97C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B 1 (533321683659908717 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry97C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (491 / 1000) (524255215037690269 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry97C_hz2 hx hc) (lowGeometry97C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (491 / 1000) (67931793655784381 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry97C_hz33 hx hc) (lowGeometry97C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (491 / 1000) (67931793655784381 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry97C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry97C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (193443144164148603 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry97C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (935506250602789493 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry97C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (459333569045969641 / 1000000000000000000) (983 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry97C_hz2 hx hc) (lowGeometry97C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (220067217418692431 / 500000000000000000) (983 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry97C_hz38 hx hc) (lowGeometry97C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry97C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1017 / 2000) (509 / 1000) θ) : B (220067217418692431 / 500000000000000000) (983 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry97C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry97C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1017 / 2000) (509 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (413267197 / 1000000000) (290312381 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (1600449 / 25000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry97C_hz12 hx hc).2
  have hrp := (lowGeometry97C_hz16 hx hc).2
  have hbn := (lowGeometry97C_hz21 hx hc).2
  have hlo := (lowGeometry97C_hz40 hx hc).1
  have hhi := (lowGeometry97C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry98W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (509 / 1000) (1019 / 2000) θ := hc

theorem lowGeometry98W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry98W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (981 / 2000) (491 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry98W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (499329 / 2000000) (500329 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry98W_hz0 hx hc) (lowGeometry98W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (500329 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry98W_hz3 hx hc) (lowGeometry98W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (699001100902209 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry98W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (2097003302706627 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry98W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (509 / 500) (1019 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry98W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry98W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry98W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1019 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry98W_hz7 hx hc) (lowGeometry98W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (3689190802706627 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry98W_hz6 hx hc) (lowGeometry98W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (3689190802706627 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry98W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry98W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (509 / 25) (1019 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry98W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1019 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry98W_hz13 hx hc) (lowGeometry98W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (3768800177706627 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry98W_hz12 hx hc) (lowGeometry98W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (3768800177706627 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry98W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry98W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1019 / 16000000) (θ * x) := bmul (lowGeometry98W_hz0 hx hc) (lowGeometry98W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (25968399592253 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry98W_hz17 hx hc) (lowGeometry98W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (11394823296623121 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry98W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (34184469889869363 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry98W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (34184469889869363 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry98W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry98W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (509 / 125) (1019 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry98W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry98W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (45571065381445717 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry98W_hz22 hx hc) (lowGeometry98W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry98W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry98W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry98W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry98W_hz26 hx hc) (lowGeometry98W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry98W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (47903839198961917 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry98W_hz24 hx hc) (lowGeometry98W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (534184469889869363 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry98W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (1141412191486082993 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry98W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (981 / 2000) (2241733544078667 / 4000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry98W_hz2 hx hc) (lowGeometry98W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (981 / 2000) (608337225218628667 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry98W_hz33 hx hc) (lowGeometry98W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (981 / 2000) (608337225218628667 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry98W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry98W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (465815530110130637 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry98W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (108492054045891011 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry98W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (425722820076076327 / 1000000000000000000) (491 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry98W_hz2 hx hc) (lowGeometry98W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (37781898087711441 / 100000000000000000) (491 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry98W_hz38 hx hc) (lowGeometry98W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (37781898087711441 / 100000000000000000) (491 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry98W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry98W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (509 / 1000) (1019 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (42144659 / 125000000) (689767059 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (59027053 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry98W_hz12 hx hc).2
  have hrp := (lowGeometry98W_hz16 hx hc).2
  have hbn := (lowGeometry98W_hz21 hx hc).2
  have hlo := (lowGeometry98W_hz40 hx hc).1
  have hhi := (lowGeometry98W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry98C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (509 / 1000) (1019 / 2000) θ := hc

theorem lowGeometry98C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry98C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (981 / 2000) (491 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry98C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (499329 / 2000000) (500329 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry98C_hz0 hx hc) (lowGeometry98C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (500329 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry98C_hz3 hx hc) (lowGeometry98C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (699001100902209 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry98C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (32209970729573791 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry98C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (509 / 500) (1019 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry98C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry98C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry98C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (7959663648083693 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry98C_hz7 hx hc) (lowGeometry98C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (64048625321908563 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry98C_hz6 hx hc) (lowGeometry98C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (64048625321908563 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry98C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry98C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (397529 / 50000) (795839 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry98C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (795839 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry98C_hz13 hx hc) (lowGeometry98C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (65043424071908563 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry98C_hz12 hx hc) (lowGeometry98C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (65043424071908563 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry98C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry98C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (1019 / 16000000) (θ * x) := bmul (lowGeometry98C_hz0 hx hc) (lowGeometry98C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (25968399592253 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry98C_hz17 hx hc) (lowGeometry98C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (11394823296623121 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry98C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (32817091094274589 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry98C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (32817091094274589 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry98C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry98C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (166443 / 100000) (333213 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry98C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry98C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (18627172974665937 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry98C_hz22 hx hc) (lowGeometry98C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry98C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry98C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry98C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry98C_hz26 hx hc) (lowGeometry98C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry98C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 0 (9608996934453777 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry98C_hz24 hx hc) (lowGeometry98C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (1032817091094274589 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry98C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B 1 (213342228731287819 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry98C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (981 / 2000) (130938792883827899 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry98C_hz2 hx hc) (lowGeometry98C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (981 / 2000) (10859463308084383 / 20000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry98C_hz33 hx hc) (lowGeometry98C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (981 / 2000) (10859463308084383 / 20000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry98C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry98C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (967182908905725411 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry98C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (467721389639670369 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry98C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (458834683236516631 / 1000000000000000000) (491 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry98C_hz2 hx hc) (lowGeometry98C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (439616689367609077 / 1000000000000000000) (491 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry98C_hz38 hx hc) (lowGeometry98C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry98C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (509 / 1000) (1019 / 2000) θ) : B (439616689367609077 / 1000000000000000000) (491 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry98C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry98C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (509 / 1000) (1019 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (412768793 / 1000000000) (290064837 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32024313 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry98C_hz12 hx hc).2
  have hrp := (lowGeometry98C_hz16 hx hc).2
  have hbn := (lowGeometry98C_hz21 hx hc).2
  have hlo := (lowGeometry98C_hz40 hx hc).1
  have hhi := (lowGeometry98C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry99W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (1019 / 2000) (51 / 100) θ := hc

theorem lowGeometry99W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry99W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49 / 100) (981 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry99W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49931 / 200000) (50031 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry99W_hz0 hx hc) (lowGeometry99W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (50031 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry99W_hz3 hx hc) (lowGeometry99W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (5591902627907607 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry99W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (16775707883722821 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry99W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (1019 / 1000) (51 / 50) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry99W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry99W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry99W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (51 / 1000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry99W_hz7 hx hc) (lowGeometry99W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (29525707883722821 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry99W_hz6 hx hc) (lowGeometry99W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (29525707883722821 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry99W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry99W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (1019 / 50) (102 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry99W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (51 / 20000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry99W_hz13 hx hc) (lowGeometry99W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (30163207883722821 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry99W_hz12 hx hc) (lowGeometry99W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (30163207883722821 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry99W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry99W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (51 / 800000) (θ * x) := bmul (lowGeometry99W_hz0 hx hc) (lowGeometry99W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (130102040816327 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry99W_hz17 hx hc) (lowGeometry99W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (5703114079525479 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry99W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (17109342238576437 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry99W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (17109342238576437 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry99W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry99W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (1019 / 250) (102 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry99W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry99W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (356373333914029 / 7812500000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry99W_hz22 hx hc) (lowGeometry99W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry99W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry99W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry99W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry99W_hz26 hx hc) (lowGeometry99W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry99W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (47950849836056089 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry99W_hz24 hx hc) (lowGeometry99W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (267109342238576437 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry99W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (1141558411377999269 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry99W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49 / 100) (279967200390454321 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry99W_hz2 hx hc) (lowGeometry99W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49 / 100) (607885250616964731 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry99W_hz33 hx hc) (lowGeometry99W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49 / 100) (607885250616964731 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry99W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry99W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (232890657761423563 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry99W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (216952233890194069 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry99W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (3401811027398243 / 8000000000000000) (981 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry99W_hz2 hx hc) (lowGeometry99W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (188637764294362143 / 500000000000000000) (981 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry99W_hz38 hx hc) (lowGeometry99W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (188637764294362143 / 500000000000000000) (981 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry99W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry99W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1019 / 2000) (51 / 100) θ) :
    OverlapGuard n θ lowWideWindow (168328459 / 500000000) (689292667 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (7381427 / 62500000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry99W_hz12 hx hc).2
  have hrp := (lowGeometry99W_hz16 hx hc).2
  have hbn := (lowGeometry99W_hz21 hx hc).2
  have hlo := (lowGeometry99W_hz40 hx hc).1
  have hhi := (lowGeometry99W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry99C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (1019 / 2000) (51 / 100) θ := hc

theorem lowGeometry99C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry99C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49 / 100) (981 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry99C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49931 / 200000) (50031 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry99C_hz0 hx hc) (lowGeometry99C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (50031 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry99C_hz3 hx hc) (lowGeometry99C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (5591902627907607 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry99C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (32209359136747817 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry99C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (1019 / 1000) (51 / 50) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry99C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry99C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry99C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (7967474897983677 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry99C_hz7 hx hc) (lowGeometry99C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (2563170349147301 / 40000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry99C_hz6 hx hc) (lowGeometry99C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (2563170349147301 / 40000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry99C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry99C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (795839 / 100000) (39831 / 5000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry99C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (39831 / 40000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry99C_hz13 hx hc) (lowGeometry99C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (2603001349147301 / 40000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry99C_hz12 hx hc) (lowGeometry99C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (2603001349147301 / 40000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry99C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry99C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (51 / 800000) (θ * x) := bmul (lowGeometry99C_hz0 hx hc) (lowGeometry99C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (130102040816327 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry99C_hz17 hx hc) (lowGeometry99C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (5703114079525479 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry99C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (821248427451669 / 25000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry99C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (821248427451669 / 25000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry99C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry99C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (333213 / 200000) (16677 / 10000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry99C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry99C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (9322726415190999 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry99C_hz22 hx hc) (lowGeometry99C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry99C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry99C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry99C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry99C_hz26 hx hc) (lowGeometry99C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry99C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 0 (19236853529230329 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry99C_hz24 hx hc) (lowGeometry99C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (25821248427451669 / 25000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry99C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B 1 (1066778992563480463 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry99C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49 / 100) (16351721745387099 / 31250000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry99C_hz2 hx hc) (lowGeometry99C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49 / 100) (542491949381617497 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry99C_hz33 hx hc) (lowGeometry99C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (49 / 100) (542491949381617497 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry99C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry99C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (24178751572548331 / 25000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry99C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (467689622085606711 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry99C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (28645989352743411 / 62500000000000000) (981 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry99C_hz2 hx hc) (lowGeometry99C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (439098976114664247 / 1000000000000000000) (981 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry99C_hz38 hx hc) (lowGeometry99C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry99C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1019 / 2000) (51 / 100) θ) : B (439098976114664247 / 1000000000000000000) (981 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry99C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry99C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1019 / 2000) (51 / 100) θ) :
    OverlapGuard n θ lowCoreWindow (412270461 / 1000000000) (579634499 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64079259 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry99C_hz12 hx hc).2
  have hrp := (lowGeometry99C_hz16 hx hc).2
  have hbn := (lowGeometry99C_hz21 hx hc).2
  have hlo := (lowGeometry99C_hz40 hx hc).1
  have hhi := (lowGeometry99C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry100W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (51 / 100) (1021 / 2000) θ := hc

theorem lowGeometry100W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry100W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (979 / 2000) (49 / 100) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (49929 / 200000) (50029 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry100W_hz0 hx hc) (lowGeometry100W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (50029 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry100W_hz3 hx hc) (lowGeometry100W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (5591790858034661 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry100W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (16775372574103983 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry100W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (51 / 50) (1021 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry100W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry100W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry100W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1021 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry100W_hz7 hx hc) (lowGeometry100W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (29537872574103983 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry100W_hz6 hx hc) (lowGeometry100W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (29537872574103983 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry100W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry100W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (102 / 5) (1021 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry100W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1021 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry100W_hz13 hx hc) (lowGeometry100W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (30175997574103983 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry100W_hz12 hx hc) (lowGeometry100W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (30175997574103983 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry100W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry100W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1021 / 16000000) (θ * x) := bmul (lowGeometry100W_hz0 hx hc) (lowGeometry100W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (130362614913177 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry100W_hz17 hx hc) (lowGeometry100W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (5708822446730521 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry100W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (17126467340191563 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry100W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (17126467340191563 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry100W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry100W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (102 / 25) (1021 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry100W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry100W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (11415127025136427 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry100W_hz22 hx hc) (lowGeometry100W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry100W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry100W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry100W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry100W_hz26 hx hc) (lowGeometry100W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry100W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (23998930236575131 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry100W_hz24 hx hc) (lowGeometry100W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (267126467340191563 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry100W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (1141704792858406877 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry100W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (979 / 2000) (55943534850061937 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry100W_hz2 hx hc) (lowGeometry100W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (979 / 2000) (18982287780430301 / 31250000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry100W_hz33 hx hc) (lowGeometry100W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (979 / 2000) (18982287780430301 / 31250000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry100W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry100W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (232873532659808437 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry100W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (216920328853835467 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry100W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (106182500973952461 / 250000000000000000) (49 / 100) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry100W_hz2 hx hc) (lowGeometry100W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (188366071711329791 / 500000000000000000) (49 / 100) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry100W_hz38 hx hc) (lowGeometry100W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (188366071711329791 / 500000000000000000) (49 / 100) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry100W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry100W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (51 / 100) (1021 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (336156689 / 1000000000) (344409047 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (118151491 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry100W_hz12 hx hc).2
  have hrp := (lowGeometry100W_hz16 hx hc).2
  have hbn := (lowGeometry100W_hz21 hx hc).2
  have hlo := (lowGeometry100W_hz40 hx hc).1
  have hhi := (lowGeometry100W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry100C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (51 / 100) (1021 / 2000) θ := hc

theorem lowGeometry100C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry100C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (979 / 2000) (49 / 100) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (49929 / 200000) (50029 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry100C_hz0 hx hc) (lowGeometry100C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (50029 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry100C_hz3 hx hc) (lowGeometry100C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (5591790858034661 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry100C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1006522354446239 / 31250000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry100C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (51 / 50) (1021 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry100C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry100C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry100C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (7975286147883661 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry100C_hz7 hx hc) (lowGeometry100C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (16027464983453573 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry100C_hz6 hx hc) (lowGeometry100C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (16027464983453573 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry100C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry100C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (39831 / 5000) (797401 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry100C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (797401 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry100C_hz13 hx hc) (lowGeometry100C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (16276652795953573 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry100C_hz12 hx hc) (lowGeometry100C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (16276652795953573 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry100C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry100C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1021 / 16000000) (θ * x) := bmul (lowGeometry100C_hz0 hx hc) (lowGeometry100C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (130362614913177 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry100C_hz17 hx hc) (lowGeometry100C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (5708822446730521 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry100C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (32882817293167801 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry100C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (32882817293167801 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry100C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry100C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (16677 / 10000) (333867 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry100C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry100C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (18663732686098059 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry100C_hz22 hx hc) (lowGeometry100C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry100C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry100C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry100C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry100C_hz26 hx hc) (lowGeometry100C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry100C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 0 (1203482074347069 / 62500000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry100C_hz24 hx hc) (lowGeometry100C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (1032882817293167801 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry100C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B 1 (533423457129735729 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry100C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (979 / 2000) (104550997597428203 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry100C_hz2 hx hc) (lowGeometry100C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (979 / 2000) (542010701176694119 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry100C_hz33 hx hc) (lowGeometry100C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (979 / 2000) (542010701176694119 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry100C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry100C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (967117182706832199 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry100C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (935315645086800253 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry100C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (457837008269988723 / 1000000000000000000) (49 / 100) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry100C_hz2 hx hc) (lowGeometry100C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (438581295080435619 / 1000000000000000000) (49 / 100) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry100C_hz38 hx hc) (lowGeometry100C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry100C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (1021 / 2000) θ) : B (438581295080435619 / 1000000000000000000) (49 / 100) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry100C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry100C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (51 / 100) (1021 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (205886101 / 500000000) (579139237 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (3205493 / 50000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry100C_hz12 hx hc).2
  have hrp := (lowGeometry100C_hz16 hx hc).2
  have hbn := (lowGeometry100C_hz21 hx hc).2
  have hlo := (lowGeometry100C_hz40 hx hc).1
  have hhi := (lowGeometry100C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry101W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (1021 / 2000) (511 / 1000) θ := hc

theorem lowGeometry101W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry101W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (489 / 1000) (979 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry101W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (499269 / 2000000) (500269 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry101W_hz0 hx hc) (lowGeometry101W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (500269 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry101W_hz3 hx hc) (lowGeometry101W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1397918374315897 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry101W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (4193755122947691 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry101W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (1021 / 1000) (511 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry101W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry101W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry101W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (511 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry101W_hz7 hx hc) (lowGeometry101W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (7387505122947691 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry101W_hz6 hx hc) (lowGeometry101W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (7387505122947691 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry101W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry101W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (1021 / 50) (511 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry101W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (511 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry101W_hz13 hx hc) (lowGeometry101W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (7547192622947691 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry101W_hz12 hx hc) (lowGeometry101W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (7547192622947691 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry101W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry101W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (511 / 8000000) (θ * x) := bmul (lowGeometry101W_hz0 hx hc) (lowGeometry101W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (130623721881391 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry101W_hz17 hx hc) (lowGeometry101W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1428634191945837 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry101W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (4285902575837511 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry101W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (4285902575837511 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry101W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry101W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (1021 / 250) (511 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry101W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry101W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (5713153682511963 / 125000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry101W_hz22 hx hc) (lowGeometry101W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry101W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry101W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry101W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry101W_hz26 hx hc) (lowGeometry101W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry101W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (9608974222048887 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry101W_hz24 hx hc) (lowGeometry101W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (66785902575837511 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry101W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (1141851336414530429 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry101W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (489 / 1000) (111787245834982529 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry101W_hz2 hx hc) (lowGeometry101W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (489 / 1000) (15174527507128927 / 25000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry101W_hz33 hx hc) (lowGeometry101W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (489 / 1000) (15174527507128927 / 25000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry101W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry101W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (58214097424162489 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry101W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (216888392890232431 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry101W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (84846739298658927 / 200000000000000000) (979 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry101W_hz2 hx hc) (lowGeometry101W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (1880944126915251 / 5000000000000000) (979 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry101W_hz38 hx hc) (lowGeometry101W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (1880944126915251 / 5000000000000000) (979 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry101W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry101W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1021 / 2000) (511 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (167828293 / 500000000) (34417167 / 50000000) ∧ radiusMinus n θ lowWideWindow ≤ (59100041 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry101W_hz12 hx hc).2
  have hrp := (lowGeometry101W_hz16 hx hc).2
  have hbn := (lowGeometry101W_hz21 hx hc).2
  have hlo := (lowGeometry101W_hz40 hx hc).1
  have hhi := (lowGeometry101W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry101C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (1021 / 2000) (511 / 1000) θ := hc

theorem lowGeometry101C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry101C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (489 / 1000) (979 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry101C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (499269 / 2000000) (500269 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry101C_hz0 hx hc) (lowGeometry101C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (500269 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry101C_hz3 hx hc) (lowGeometry101C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1397918374315897 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry101C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (32208039344238267 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry101C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (1021 / 1000) (511 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry101C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry101C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry101C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1596619479556729 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry101C_hz7 hx hc) (lowGeometry101C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (64140428935372847 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry101C_hz6 hx hc) (lowGeometry101C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (64140428935372847 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry101C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry101C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (797401 / 100000) (399091 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry101C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (399091 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry101C_hz13 hx hc) (lowGeometry101C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (65138156435372847 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry101C_hz12 hx hc) (lowGeometry101C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (65138156435372847 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry101C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry101C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (511 / 8000000) (θ * x) := bmul (lowGeometry101C_hz0 hx hc) (lowGeometry101C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (130623721881391 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry101C_hz17 hx hc) (lowGeometry101C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (1428634191945837 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry101C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (6583146356486417 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry101C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (6583146356486417 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry101C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry101C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (333867 / 200000) (167097 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry101C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry101C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (18682012541814119 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry101C_hz22 hx hc) (lowGeometry101C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry101C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry101C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry101C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry101C_hz26 hx hc) (lowGeometry101C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry101C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 0 (9637286424937939 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry101C_hz24 hx hc) (lowGeometry101C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (206583146356486417 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry101C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B 1 (53345745448181859 / 50000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry101C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (489 / 1000) (1305637119844251 / 2500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry101C_hz2 hx hc) (lowGeometry101C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (489 / 1000) (270764710393788139 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry101C_hz33 hx hc) (lowGeometry101C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (489 / 1000) (270764710393788139 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry101C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry101C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (193416853643513583 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry101C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (935251981833908839 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry101C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (228669109558390711 / 500000000000000000) (979 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry101C_hz2 hx hc) (lowGeometry101C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (54757955783363193 / 125000000000000000) (979 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry101C_hz38 hx hc) (lowGeometry101C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry101C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1021 / 2000) (511 / 1000) θ) : B (54757955783363193 / 125000000000000000) (979 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry101C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry101C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1021 / 2000) (511 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (82254803 / 200000000) (36165243 / 62500000) ∧ radiusMinus n θ lowCoreWindow ≤ (64140429 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry101C_hz12 hx hc).2
  have hrp := (lowGeometry101C_hz16 hx hc).2
  have hbn := (lowGeometry101C_hz21 hx hc).2
  have hlo := (lowGeometry101C_hz40 hx hc).1
  have hhi := (lowGeometry101C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry102W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (511 / 1000) (1023 / 2000) θ := hc

theorem lowGeometry102W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry102W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (977 / 2000) (489 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry102W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (499247 / 2000000) (500247 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry102W_hz0 hx hc) (lowGeometry102W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (500247 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry102W_hz3 hx hc) (lowGeometry102W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (5591550545242349 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry102W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (16774651635727047 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry102W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (511 / 500) (1023 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry102W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry102W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry102W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1023 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry102W_hz7 hx hc) (lowGeometry102W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (29562151635727047 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry102W_hz6 hx hc) (lowGeometry102W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (29562151635727047 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry102W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry102W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (511 / 25) (1023 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry102W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1023 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry102W_hz13 hx hc) (lowGeometry102W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (30201526635727047 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry102W_hz12 hx hc) (lowGeometry102W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (30201526635727047 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry102W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry102W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1023 / 16000000) (θ * x) := bmul (lowGeometry102W_hz0 hx hc) (lowGeometry102W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (4090167604913 / 31250000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry102W_hz17 hx hc) (lowGeometry102W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (11440514121192981 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry102W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (34321542363578943 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry102W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (34321542363578943 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry102W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry102W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (511 / 125) (1023 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry102W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry102W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (457499508196457 / 10000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry102W_hz22 hx hc) (lowGeometry102W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry102W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry102W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry102W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry102W_hz26 hx hc) (lowGeometry102W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry102W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (3005742609208663 / 62500000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry102W_hz24 hx hc) (lowGeometry102W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (534321542363578943 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry102W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (1141998042535175549 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry102W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (977 / 2000) (139609260699925211 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry102W_hz2 hx hc) (lowGeometry102W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (977 / 2000) (151632231136759863 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry102W_hz33 hx hc) (lowGeometry102W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (977 / 2000) (151632231136759863 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry102W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry102W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (465678457636421057 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry102W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (216856425906636001 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry102W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (84747491244313349 / 200000000000000000) (489 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry102W_hz2 hx hc) (lowGeometry102W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (375645574474228137 / 1000000000000000000) (489 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry102W_hz38 hx hc) (lowGeometry102W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (375645574474228137 / 1000000000000000000) (489 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry102W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry102W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (511 / 1000) (1023 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (335156609 / 1000000000) (137573681 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (118248607 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry102W_hz12 hx hc).2
  have hrp := (lowGeometry102W_hz16 hx hc).2
  have hbn := (lowGeometry102W_hz21 hx hc).2
  have hlo := (lowGeometry102W_hz40 hx hc).1
  have hhi := (lowGeometry102W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry102C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (511 / 1000) (1023 / 2000) θ := hc

theorem lowGeometry102C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry102C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (977 / 2000) (489 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry102C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (499247 / 2000000) (500247 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry102C_hz0 hx hc) (lowGeometry102C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (500247 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry102C_hz3 hx hc) (lowGeometry102C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (5591550545242349 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry102C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (32207331140595931 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry102C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (511 / 500) (1023 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry102C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry102C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry102C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (7990908647683629 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry102C_hz7 hx hc) (lowGeometry102C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (64170965731330447 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry102C_hz6 hx hc) (lowGeometry102C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (64170965731330447 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry102C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry102C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (399091 / 50000) (798963 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry102C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (798963 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry102C_hz13 hx hc) (lowGeometry102C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (65169669481330447 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry102C_hz12 hx hc) (lowGeometry102C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (65169669481330447 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry102C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry102C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (1023 / 16000000) (θ * x) := bmul (lowGeometry102C_hz0 hx hc) (lowGeometry102C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (4090167604913 / 31250000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry102C_hz17 hx hc) (lowGeometry102C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (11440514121192981 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry102C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (16474340334517893 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry102C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (16474340334517893 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry102C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry102C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (167097 / 100000) (334521 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry102C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry102C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (935014619876509 / 50000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry102C_hz22 hx hc) (lowGeometry102C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry102C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry102C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry102C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry102C_hz26 hx hc) (lowGeometry102C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry102C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 0 (19293432510198653 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry102C_hz24 hx hc) (lowGeometry102C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (516474340334517893 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry102C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B 1 (213396595379180333 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry102C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (977 / 2000) (104350935140419183 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry102C_hz2 hx hc) (lowGeometry102C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (977 / 2000) (67631013526536821 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry102C_hz33 hx hc) (lowGeometry102C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (977 / 2000) (67631013526536821 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry102C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry102C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (483525659665482107 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry102C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (23379706355493963 / 25000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry102C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (456839462186352037 / 1000000000000000000) (489 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry102C_hz2 hx hc) (lowGeometry102C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (54693253709519173 / 125000000000000000) (489 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry102C_hz38 hx hc) (lowGeometry102C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry102C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (511 / 1000) (1023 / 2000) θ) : B (54693253709519173 / 125000000000000000) (489 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry102C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry102C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (511 / 1000) (1023 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (4107759 / 10000000) (578148453 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32085483 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry102C_hz12 hx hc).2
  have hrp := (lowGeometry102C_hz16 hx hc).2
  have hbn := (lowGeometry102C_hz21 hx hc).2
  have hlo := (lowGeometry102C_hz40 hx hc).1
  have hhi := (lowGeometry102C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry103W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (1023 / 2000) (64 / 125) θ := hc

theorem lowGeometry103W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry103W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (61 / 125) (977 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry103W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (62403 / 250000) (3908 / 15625) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry103W_hz0 hx hc) (lowGeometry103W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (977 / 31250000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry103W_hz3 hx hc) (lowGeometry103W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (5591422001602097 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry103W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (16774266004806291 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry103W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (1023 / 1000) (128 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry103W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry103W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry103W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (32 / 625) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry103W_hz7 hx hc) (lowGeometry103W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (29574266004806291 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry103W_hz6 hx hc) (lowGeometry103W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (29574266004806291 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry103W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry103W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (1023 / 50) (512 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry103W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (8 / 3125) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry103W_hz13 hx hc) (lowGeometry103W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (30214266004806291 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry103W_hz12 hx hc) (lowGeometry103W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (30214266004806291 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry103W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry103W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1 / 15625) (θ * x) := bmul (lowGeometry103W_hz0 hx hc) (lowGeometry103W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (131147540983607 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry103W_hz17 hx hc) (lowGeometry103W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1431495835784673 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry103W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (4294487507354019 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry103W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (4294487507354019 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry103W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry103W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (1023 / 250) (512 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry103W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry103W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (2862167011199731 / 62500000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry103W_hz22 hx hc) (lowGeometry103W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry103W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry103W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry103W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry103W_hz26 hx hc) (lowGeometry103W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry103W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (48138892384432781 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry103W_hz24 hx hc) (lowGeometry103W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (66794487507354019 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry103W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (1142144911710738461 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry103W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (61 / 125) (557937789370695739 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry103W_hz2 hx hc) (lowGeometry103W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (61 / 125) (15151917043878213 / 25000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry103W_hz33 hx hc) (lowGeometry103W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (61 / 125) (15151917043878213 / 25000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry103W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry103W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (58205512492645981 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry103W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (216824427810020311 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry103W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (423241283085159647 / 1000000000000000000) (977 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry103W_hz2 hx hc) (lowGeometry103W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (187551195350363433 / 500000000000000000) (977 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry103W_hz38 hx hc) (lowGeometry103W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (187551195350363433 / 500000000000000000) (977 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry103W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry103W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1023 / 2000) (64 / 125) θ) :
    OverlapGuard n θ lowWideWindow (334656757 / 1000000000) (68739329 / 100000000) ∧ radiusMinus n θ lowWideWindow ≤ (23659413 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry103W_hz12 hx hc).2
  have hrp := (lowGeometry103W_hz16 hx hc).2
  have hbn := (lowGeometry103W_hz21 hx hc).2
  have hlo := (lowGeometry103W_hz40 hx hc).1
  have hhi := (lowGeometry103W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry103C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (1023 / 2000) (64 / 125) θ := hc

theorem lowGeometry103C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry103C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (61 / 125) (977 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry103C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (62403 / 250000) (3908 / 15625) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry103C_hz0 hx hc) (lowGeometry103C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (977 / 31250000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry103C_hz3 hx hc) (lowGeometry103C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (5591422001602097 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry103C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (32206590729228079 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry103C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (1023 / 1000) (128 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry103C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry103C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry103C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (7998719897583613 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry103C_hz7 hx hc) (lowGeometry103C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (64201470319562531 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry103C_hz6 hx hc) (lowGeometry103C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (64201470319562531 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry103C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry103C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (798963 / 100000) (24992 / 3125) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry103C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (781 / 781250) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry103C_hz13 hx hc) (lowGeometry103C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (65201150319562531 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry103C_hz12 hx hc) (lowGeometry103C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (65201150319562531 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry103C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry103C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1 / 15625) (θ * x) := bmul (lowGeometry103C_hz0 hx hc) (lowGeometry103C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (131147540983607 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry103C_hz17 hx hc) (lowGeometry103C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (1431495835784673 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry103C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (16490832028239433 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry103C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (16490832028239433 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry103C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry103C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (334521 / 200000) (5232 / 3125) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry103C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry103C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (18718572253246241 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry103C_hz22 hx hc) (lowGeometry103C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry103C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry103C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry103C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry103C_hz26 hx hc) (lowGeometry103C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry103C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 0 (4828073042630357 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry103C_hz24 hx hc) (lowGeometry103C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (516490832028239433 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry103C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B 1 (533525559138446081 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry103C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (61 / 125) (260627235639130911 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry103C_hz2 hx hc) (lowGeometry103C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (61 / 125) (2162267053795133 / 4000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry103C_hz33 hx hc) (lowGeometry103C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (61 / 125) (2162267053795133 / 4000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry103C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry103C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (483509167971760567 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry103C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (935124462050976697 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry103C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (114085184370219157 / 250000000000000000) (977 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry103C_hz2 hx hc) (lowGeometry103C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (68285694579743 / 156250000000000) (977 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry103C_hz38 hx hc) (lowGeometry103C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry103C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1023 / 2000) (64 / 125) θ) : B (68285694579743 / 156250000000000) (977 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry103C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry103C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1023 / 2000) (64 / 125) θ) :
    OverlapGuard n θ lowCoreWindow (410277857 / 1000000000) (577652931 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64201471 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry103C_hz12 hx hc).2
  have hrp := (lowGeometry103C_hz16 hx hc).2
  have hbn := (lowGeometry103C_hz21 hx hc).2
  have hlo := (lowGeometry103C_hz40 hx hc).1
  have hhi := (lowGeometry103C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry104W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (64 / 125) (41 / 80) θ := hc

theorem lowGeometry104W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry104W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (39 / 80) (61 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry104W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (156 / 625) (2501 / 10000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry104W_hz0 hx hc) (lowGeometry104W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (2501 / 80000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry104W_hz3 hx hc) (lowGeometry104W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (5591287865957181 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry104W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (16773863597871543 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry104W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (128 / 125) (41 / 40) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry104W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry104W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry104W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (41 / 800) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry104W_hz7 hx hc) (lowGeometry104W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (29586363597871543 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry104W_hz6 hx hc) (lowGeometry104W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (29586363597871543 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry104W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry104W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (512 / 25) (41 / 2) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry104W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (41 / 16000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry104W_hz13 hx hc) (lowGeometry104W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (30226988597871543 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry104W_hz12 hx hc) (lowGeometry104W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (30226988597871543 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry104W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry104W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (41 / 640000) (θ * x) := bmul (lowGeometry104W_hz0 hx hc) (lowGeometry104W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (131410256410257 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry104W_hz17 hx hc) (lowGeometry104W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (11463431266870187 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry104W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (34390293800610561 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry104W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (34390293800610561 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry104W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry104W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (512 / 125) (41 / 10) (θ * (8 : ℝ)) := bmul (lowGeometry104W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry104W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (45839393538745691 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry104W_hz22 hx hc) (lowGeometry104W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry104W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry104W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry104W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry104W_hz26 hx hc) (lowGeometry104W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry104W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (6023237877690869 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry104W_hz24 hx hc) (lowGeometry104W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (534390293800610561 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry104W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (1142291944433211497 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry104W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (39 / 80) (557438468883407211 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry104W_hz2 hx hc) (lowGeometry104W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (39 / 80) (605624371904934163 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry104W_hz33 hx hc) (lowGeometry104W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (39 / 80) (605624371904934163 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry104W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry104W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (465609706199389439 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry104W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (27099049813385219 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry104W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (52843147136101177 / 125000000000000000) (61 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry104W_hz2 hx hc) (lowGeometry104W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (11704977314602577 / 31250000000000000) (61 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry104W_hz38 hx hc) (lowGeometry104W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (11704977314602577 / 31250000000000000) (61 / 125) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry104W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry104W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (64 / 125) (41 / 80) θ) :
    OverlapGuard n θ lowWideWindow (334157031 / 1000000000) (137383599 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (23669091 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry104W_hz12 hx hc).2
  have hrp := (lowGeometry104W_hz16 hx hc).2
  have hbn := (lowGeometry104W_hz21 hx hc).2
  have hlo := (lowGeometry104W_hz40 hx hc).1
  have hhi := (lowGeometry104W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry104C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (64 / 125) (41 / 80) θ := hc

theorem lowGeometry104C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry104C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (39 / 80) (61 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry104C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (156 / 625) (2501 / 10000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry104C_hz0 hx hc) (lowGeometry104C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (2501 / 80000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry104C_hz3 hx hc) (lowGeometry104C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (5591287865957181 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry104C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (32205818107913363 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry104C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (128 / 125) (41 / 40) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry104C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry104C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry104C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (8006531147483597 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry104C_hz7 hx hc) (lowGeometry104C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (64231942697847751 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry104C_hz6 hx hc) (lowGeometry104C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (64231942697847751 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry104C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry104C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (24992 / 3125) (32021 / 4000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry104C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (32021 / 32000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry104C_hz13 hx hc) (lowGeometry104C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (65232598947847751 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry104C_hz12 hx hc) (lowGeometry104C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (65232598947847751 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry104C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry104C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (41 / 640000) (θ * x) := bmul (lowGeometry104C_hz0 hx hc) (lowGeometry104C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (131410256410257 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry104C_hz17 hx hc) (lowGeometry104C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (11463431266870187 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry104C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (33014682048586139 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry104C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (33014682048586139 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry104C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry104C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (5232 / 3125) (13407 / 8000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry104C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry104C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (9368426054481151 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry104C_hz22 hx hc) (lowGeometry104C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry104C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry104C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry104C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry104C_hz26 hx hc) (lowGeometry104C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry104C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 0 (19331151830844203 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry104C_hz24 hx hc) (lowGeometry104C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (1033014682048586139 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry104C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B 1 (533559666663970757 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry104C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (39 / 80) (520754234664035459 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry104C_hz2 hx hc) (lowGeometry104C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (39 / 80) (270042693247439831 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry104C_hz33 hx hc) (lowGeometry104C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (39 / 80) (270042693247439831 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry104C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry104C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (966985317951413861 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry104C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (935060605133596957 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry104C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (113960511250657129 / 250000000000000000) (61 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry104C_hz2 hx hc) (lowGeometry104C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (436510893171784313 / 1000000000000000000) (61 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry104C_hz38 hx hc) (lowGeometry104C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry104C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (64 / 125) (41 / 80) θ) : B (436510893171784313 / 1000000000000000000) (61 / 125) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry104C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry104C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (64 / 125) (41 / 80) θ) :
    OverlapGuard n θ lowCoreWindow (204889943 / 500000000) (577157323 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64231943 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry104C_hz12 hx hc).2
  have hrp := (lowGeometry104C_hz16 hx hc).2
  have hbn := (lowGeometry104C_hz21 hx hc).2
  have hlo := (lowGeometry104C_hz40 hx hc).1
  have hhi := (lowGeometry104C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry105W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (41 / 80) (513 / 1000) θ := hc

theorem lowGeometry105W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry105W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (487 / 1000) (39 / 80) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry105W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (19967 / 80000) (20007 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry105W_hz0 hx hc) (lowGeometry105W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (20007 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry105W_hz3 hx hc) (lowGeometry105W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (559114813790513 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry105W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (1677344441371539 / 25000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry105W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (41 / 40) (513 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry105W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry105W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry105W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (513 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry105W_hz7 hx hc) (lowGeometry105W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (2959844441371539 / 25000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry105W_hz6 hx hc) (lowGeometry105W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (2959844441371539 / 25000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry105W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry105W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (41 / 2) (513 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry105W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (513 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry105W_hz13 hx hc) (lowGeometry105W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (3023969441371539 / 25000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry105W_hz12 hx hc) (lowGeometry105W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (3023969441371539 / 25000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry105W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry105W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (513 / 8000000) (θ * x) := bmul (lowGeometry105W_hz0 hx hc) (lowGeometry105W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (26334702258727 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry105W_hz17 hx hc) (lowGeometry105W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (11474907899135183 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry105W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (34424723697405549 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry105W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (34424723697405549 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry105W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry105W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (41 / 10) (513 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry105W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry105W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (45884114898295687 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry105W_hz22 hx hc) (lowGeometry105W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry105W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry105W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry105W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry105W_hz26 hx hc) (lowGeometry105W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry105W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (385863309268969 / 8000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry105W_hz24 hx hc) (lowGeometry105W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (534424723697405549 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry105W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (1142439141196193057 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry105W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (487 / 1000) (139234770333286029 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry105W_hz2 hx hc) (lowGeometry105W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (487 / 1000) (605171994991765241 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry105W_hz33 hx hc) (lowGeometry105W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (487 / 1000) (605171994991765241 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry105W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry105W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (465575276302594451 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry105W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (108380168952118583 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry105W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (422249138237453999 / 1000000000000000000) (39 / 80) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry105W_hz2 hx hc) (lowGeometry105W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (187008112289416437 / 500000000000000000) (39 / 80) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry105W_hz38 hx hc) (lowGeometry105W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (187008112289416437 / 500000000000000000) (39 / 80) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry105W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry105W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (41 / 80) (513 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (333657429 / 1000000000) (343221259 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (59196889 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry105W_hz12 hx hc).2
  have hrp := (lowGeometry105W_hz16 hx hc).2
  have hbn := (lowGeometry105W_hz21 hx hc).2
  have hlo := (lowGeometry105W_hz40 hx hc).1
  have hhi := (lowGeometry105W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry105C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (41 / 80) (513 / 1000) θ := hc

theorem lowGeometry105C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry105C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (487 / 1000) (39 / 80) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry105C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (19967 / 80000) (20007 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry105C_hz0 hx hc) (lowGeometry105C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (20007 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry105C_hz3 hx hc) (lowGeometry105C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (559114813790513 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry105C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (32205013274333549 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry105C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (41 / 40) (513 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry105C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry105C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry105C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (8014342397383581 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry105C_hz7 hx hc) (lowGeometry105C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (64262382863867873 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry105C_hz6 hx hc) (lowGeometry105C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (64262382863867873 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry105C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry105C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (32021 / 4000) (400653 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry105C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (400653 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry105C_hz13 hx hc) (lowGeometry105C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (65264015363867873 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry105C_hz12 hx hc) (lowGeometry105C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (65264015363867873 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry105C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry105C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (513 / 8000000) (θ * x) := bmul (lowGeometry105C_hz0 hx hc) (lowGeometry105C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (26334702258727 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry105C_hz17 hx hc) (lowGeometry105C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (11474907899135183 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry105C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (2065483421844333 / 62500000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry105C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (2065483421844333 / 62500000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry105C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry105C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (13407 / 8000) (167751 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry105C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry105C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (9377565982339181 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry105C_hz22 hx hc) (lowGeometry105C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry105C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry105C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry105C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry105C_hz26 hx hc) (lowGeometry105C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry105C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 0 (19350011491166977 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry105C_hz24 hx hc) (lowGeometry105C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (64565483421844333 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry105C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B 1 (1067187622271092583 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry105C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (487 / 1000) (104050793171431527 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry105C_hz2 hx hc) (lowGeometry105C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (487 / 1000) (134900994337081153 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry105C_hz33 hx hc) (lowGeometry105C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (487 / 1000) (134900994337081153 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry105C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry105C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (60434516578155667 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry105C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (93499668327305527 / 100000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry105C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (113835846188494479 / 250000000000000000) (39 / 80) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry105C_hz2 hx hc) (lowGeometry105C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (435993373262810939 / 1000000000000000000) (39 / 80) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry105C_hz38 hx hc) (lowGeometry105C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry105C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (41 / 80) (513 / 1000) θ) : B (435993373262810939 / 1000000000000000000) (39 / 80) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry105C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry105C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (41 / 80) (513 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (409281987 / 1000000000) (144165407 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64262383 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry105C_hz12 hx hc).2
  have hrp := (lowGeometry105C_hz16 hx hc).2
  have hbn := (lowGeometry105C_hz21 hx hc).2
  have hlo := (lowGeometry105C_hz40 hx hc).1
  have hhi := (lowGeometry105C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry106W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (513 / 1000) (1027 / 2000) θ := hc

theorem lowGeometry106W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry106W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (973 / 2000) (487 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry106W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (499149 / 2000000) (500149 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry106W_hz0 hx hc) (lowGeometry106W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (500149 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry106W_hz3 hx hc) (lowGeometry106W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (174718838032083 / 31250000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry106W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (524156514096249 / 7812500000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry106W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (513 / 500) (1027 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry106W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry106W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry106W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1027 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry106W_hz7 hx hc) (lowGeometry106W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (925328389096249 / 7812500000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry106W_hz6 hx hc) (lowGeometry106W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (925328389096249 / 7812500000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry106W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry106W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (513 / 25) (1027 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry106W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1027 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry106W_hz13 hx hc) (lowGeometry106W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (945386982846249 / 7812500000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry106W_hz12 hx hc) (lowGeometry106W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (945386982846249 / 7812500000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry106W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry106W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1027 / 16000000) (θ * x) := bmul (lowGeometry106W_hz0 hx hc) (lowGeometry106W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (6596865364851 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry106W_hz17 hx hc) (lowGeometry106W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (11486396619350213 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry106W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (34459189858050639 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry106W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (34459189858050639 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry106W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry106W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (513 / 125) (1027 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry106W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry106W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (45928836257845683 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry106W_hz22 hx hc) (lowGeometry106W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry106W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry106W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry106W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry106W_hz26 hx hc) (lowGeometry106W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry106W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (24139962147857649 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry106W_hz24 hx hc) (lowGeometry106W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (534459189858050639 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry106W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (1142586502494895277 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry106W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (973 / 2000) (278219813357507 / 500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry106W_hz2 hx hc) (lowGeometry106W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (973 / 2000) (302359775505364649 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry106W_hz33 hx hc) (lowGeometry106W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (973 / 2000) (302359775505364649 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry106W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry106W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (465540810141949361 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry106W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (216728245907622541 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry106W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (52719145817029183 / 125000000000000000) (487 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry106W_hz2 hx hc) (lowGeometry106W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (186736621120259083 / 500000000000000000) (487 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry106W_hz38 hx hc) (lowGeometry106W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (186736621120259083 / 500000000000000000) (487 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry106W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry106W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (513 / 1000) (1027 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (333157953 / 1000000000) (342983431 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (59221017 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry106W_hz12 hx hc).2
  have hrp := (lowGeometry106W_hz16 hx hc).2
  have hbn := (lowGeometry106W_hz21 hx hc).2
  have hlo := (lowGeometry106W_hz40 hx hc).1
  have hhi := (lowGeometry106W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry106C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (513 / 1000) (1027 / 2000) θ := hc

theorem lowGeometry106C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry106C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (973 / 2000) (487 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry106C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (499149 / 2000000) (500149 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry106C_hz0 hx hc) (lowGeometry106C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (500149 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry106C_hz3 hx hc) (lowGeometry106C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (174718838032083 / 31250000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry106C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (32204176226073539 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry106C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (513 / 500) (1027 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry106C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry106C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry106C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1604430729456713 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry106C_hz7 hx hc) (lowGeometry106C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (64292790815207799 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry106C_hz6 hx hc) (lowGeometry106C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (64292790815207799 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry106C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry106C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (400653 / 50000) (802087 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry106C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (802087 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry106C_hz13 hx hc) (lowGeometry106C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (65295399565207799 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry106C_hz12 hx hc) (lowGeometry106C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (65295399565207799 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry106C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry106C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (1027 / 16000000) (θ * x) := bmul (lowGeometry106C_hz0 hx hc) (lowGeometry106C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (6596865364851 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry106C_hz17 hx hc) (lowGeometry106C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (11486396619350213 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry106C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (16540411131864307 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry106C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (16540411131864307 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry106C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry106C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (167751 / 100000) (335829 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry106C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry106C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (18773411820394423 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry106C_hz22 hx hc) (lowGeometry106C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry106C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry106C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry106C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry106C_hz26 hx hc) (lowGeometry106C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry106C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 0 (19368871151489753 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry106C_hz24 hx hc) (lowGeometry106C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (516540411131864307 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry106C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B 1 (1067255985329101631 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry106C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (973 / 2000) (103950732971054499 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry106C_hz2 hx hc) (lowGeometry106C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (973 / 2000) (67390317000845281 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry106C_hz33 hx hc) (lowGeometry106C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (973 / 2000) (67390317000845281 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry106C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry106C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (483459588868135693 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry106C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (467466348137093587 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry106C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (22742237836869603 / 50000000000000000) (487 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry106C_hz2 hx hc) (lowGeometry106C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (435475885585902307 / 1000000000000000000) (487 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry106C_hz38 hx hc) (lowGeometry106C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry106C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (513 / 1000) (1027 / 2000) θ) : B (435475885585902307 / 1000000000000000000) (487 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry106C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry106C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (513 / 1000) (1027 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (2554901 / 6250000) (576165847 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64292791 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry106C_hz12 hx hc).2
  have hrp := (lowGeometry106C_hz16 hx hc).2
  have hbn := (lowGeometry106C_hz21 hx hc).2
  have hlo := (lowGeometry106C_hz40 hx hc).1
  have hhi := (lowGeometry106C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry107W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (1027 / 2000) (257 / 500) θ := hc

theorem lowGeometry107W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry107W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (243 / 500) (973 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry107W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (249561 / 1000000) (250061 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry107W_hz0 hx hc) (lowGeometry107W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (250061 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry107W_hz3 hx hc) (lowGeometry107W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (2795425951442821 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry107W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (8386277854328463 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry107W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (1027 / 1000) (257 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry107W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry107W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry107W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (257 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry107W_hz7 hx hc) (lowGeometry107W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (14811277854328463 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry107W_hz6 hx hc) (lowGeometry107W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (14811277854328463 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry107W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry107W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (1027 / 50) (514 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry107W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (257 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry107W_hz13 hx hc) (lowGeometry107W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (15132527854328463 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry107W_hz12 hx hc) (lowGeometry107W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (15132527854328463 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry107W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry107W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (257 / 4000000) (θ * x) := bmul (lowGeometry107W_hz0 hx hc) (lowGeometry107W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (26440329218107 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry107W_hz17 hx hc) (lowGeometry107W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (2299579492781539 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry107W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (6898738478344617 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry107W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (6898738478344617 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry107W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry107W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (1027 / 250) (514 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry107W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry107W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (45973557617395679 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry107W_hz22 hx hc) (lowGeometry107W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry107W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry107W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry107W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry107W_hz26 hx hc) (lowGeometry107W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry107W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (48326934932809471 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry107W_hz24 hx hc) (lowGeometry107W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (106898738478344617 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry107W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (1142734028826151601 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry107W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (243 / 500) (277970052511961377 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry107W_hz2 hx hc) (lowGeometry107W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (243 / 500) (24170681598269289 / 40000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry107W_hz33 hx hc) (lowGeometry107W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (243 / 500) (24170681598269289 / 40000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry107W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry107W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (93101261521655383 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry107W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (21669612242309173 / 25000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry107W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (421257261990490323 / 1000000000000000000) (973 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry107W_hz2 hx hc) (lowGeometry107W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (93232581764420213 / 250000000000000000) (973 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry107W_hz38 hx hc) (lowGeometry107W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (93232581764420213 / 250000000000000000) (973 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry107W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry107W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1027 / 2000) (257 / 500) θ) :
    OverlapGuard n θ lowWideWindow (166329301 / 500000000) (27419641 / 40000000) ∧ radiusMinus n θ lowWideWindow ≤ (118490223 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry107W_hz12 hx hc).2
  have hrp := (lowGeometry107W_hz16 hx hc).2
  have hbn := (lowGeometry107W_hz21 hx hc).2
  have hlo := (lowGeometry107W_hz40 hx hc).1
  have hhi := (lowGeometry107W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry107C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (1027 / 2000) (257 / 500) θ := hc

theorem lowGeometry107C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry107C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (243 / 500) (973 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry107C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (249561 / 1000000) (250061 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry107C_hz0 hx hc) (lowGeometry107C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (250061 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry107C_hz3 hx hc) (lowGeometry107C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (2795425951442821 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry107C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (16101653480310649 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry107C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (1027 / 1000) (257 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry107C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry107C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry107C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (8029964897183549 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry107C_hz7 hx hc) (lowGeometry107C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (32161583274677747 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry107C_hz6 hx hc) (lowGeometry107C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (32161583274677747 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry107C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry107C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (802087 / 100000) (200717 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry107C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (200717 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry107C_hz13 hx hc) (lowGeometry107C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (32663375774677747 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry107C_hz12 hx hc) (lowGeometry107C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (32663375774677747 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry107C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry107C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (257 / 4000000) (θ * x) := bmul (lowGeometry107C_hz0 hx hc) (lowGeometry107C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (26440329218107 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry107C_hz17 hx hc) (lowGeometry107C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (2299579492781539 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry107C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (16556972348027081 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry107C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (16556972348027081 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry107C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry107C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (335829 / 200000) (84039 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry107C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry107C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (4697922919027621 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry107C_hz22 hx hc) (lowGeometry107C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry107C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry107C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry107C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry107C_hz26 hx hc) (lowGeometry107C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry107C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 0 (1211733175738283 / 62500000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry107C_hz24 hx hc) (lowGeometry107C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (516556972348027081 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry107C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B 1 (533662211362720829 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry107C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (243 / 500) (519253331655927367 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry107C_hz2 hx hc) (lowGeometry107C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (243 / 500) (107728212493547979 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry107C_hz33 hx hc) (lowGeometry107C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (243 / 500) (107728212493547979 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry107C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry107C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (483443027651972919 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry107C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (934868643941225009 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry107C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (227173080477717677 / 500000000000000000) (973 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry107C_hz2 hx hc) (lowGeometry107C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (217479215071811413 / 500000000000000000) (973 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry107C_hz38 hx hc) (lowGeometry107C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry107C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1027 / 2000) (257 / 500) θ) : B (217479215071811413 / 500000000000000000) (973 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry107C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry107C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1027 / 2000) (257 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (81657281 / 200000000) (575669979 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64323167 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry107C_hz12 hx hc).2
  have hrp := (lowGeometry107C_hz16 hx hc).2
  have hbn := (lowGeometry107C_hz21 hx hc).2
  have hlo := (lowGeometry107C_hz40 hx hc).1
  have hhi := (lowGeometry107C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry108W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (257 / 500) (1029 / 2000) θ := hc

theorem lowGeometry108W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry108W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (971 / 2000) (243 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry108W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (249547 / 1000000) (250047 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry108W_hz0 hx hc) (lowGeometry108W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (250047 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry108W_hz3 hx hc) (lowGeometry108W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (2795347697514569 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry108W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (8386043092543707 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry108W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (257 / 250) (1029 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry108W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry108W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry108W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1029 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry108W_hz7 hx hc) (lowGeometry108W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (14817293092543707 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry108W_hz6 hx hc) (lowGeometry108W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (14817293092543707 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry108W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry108W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (514 / 25) (1029 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry108W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1029 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry108W_hz13 hx hc) (lowGeometry108W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (15138855592543707 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry108W_hz12 hx hc) (lowGeometry108W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (15138855592543707 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry108W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry108W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1029 / 16000000) (θ * x) := bmul (lowGeometry108W_hz0 hx hc) (lowGeometry108W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (26493305870237 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry108W_hz17 hx hc) (lowGeometry108W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (2877352617328829 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry108W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (8632057851986487 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry108W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (8632057851986487 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry108W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry108W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (514 / 125) (1029 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry108W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry108W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1840731159077827 / 40000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry108W_hz22 hx hc) (lowGeometry108W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry108W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry108W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry108W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry108W_hz26 hx hc) (lowGeometry108W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry108W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (12093486392475911 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry108W_hz24 hx hc) (lowGeometry108W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (133632057851986487 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry108W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (1142881720688426453 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry108W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (971 / 2000) (555440516254575257 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry108W_hz2 hx hc) (lowGeometry108W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (971 / 2000) (603814461824478901 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry108W_hz33 hx hc) (lowGeometry108W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (971 / 2000) (603814461824478901 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry108W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry108W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (116367942148013513 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry108W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (216663967356214717 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry108W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (21038071230288449 / 50000000000000000) (243 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry108W_hz2 hx hc) (lowGeometry108W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (46548434879483167 / 125000000000000000) (243 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry108W_hz38 hx hc) (lowGeometry108W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (46548434879483167 / 125000000000000000) (243 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry108W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry108W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (257 / 500) (1029 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (20759961 / 62500000) (685015007 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (23707669 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry108W_hz12 hx hc).2
  have hrp := (lowGeometry108W_hz16 hx hc).2
  have hbn := (lowGeometry108W_hz21 hx hc).2
  have hlo := (lowGeometry108W_hz40 hx hc).1
  have hhi := (lowGeometry108W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry108C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (257 / 500) (1029 / 2000) θ := hc

theorem lowGeometry108C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry108C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (971 / 2000) (243 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry108C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (249547 / 1000000) (250047 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry108C_hz0 hx hc) (lowGeometry108C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (250047 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry108C_hz3 hx hc) (lowGeometry108C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (2795347697514569 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry108C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (6440481095073567 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry108C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (257 / 250) (1029 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry108C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry108C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry108C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (8037776147083533 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry108C_hz7 hx hc) (lowGeometry108C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (64353510063701967 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry108C_hz6 hx hc) (lowGeometry108C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (64353510063701967 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry108C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry108C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (200717 / 25000) (803649 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry108C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (803649 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry108C_hz13 hx hc) (lowGeometry108C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (65358071313701967 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry108C_hz12 hx hc) (lowGeometry108C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (65358071313701967 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry108C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry108C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (1029 / 16000000) (θ * x) := bmul (lowGeometry108C_hz0 hx hc) (lowGeometry108C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (26493305870237 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry108C_hz17 hx hc) (lowGeometry108C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (2877352617328829 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry108C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (33147102151628111 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry108C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (33147102151628111 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry108C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry108C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (84039 / 50000) (336483 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry108C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry108C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (3761994306365309 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry108C_hz22 hx hc) (lowGeometry108C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry108C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry108C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry108C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry108C_hz26 hx hc) (lowGeometry108C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry108C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 0 (19406590472135303 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry108C_hz24 hx hc) (lowGeometry108C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (1033147102151628111 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry108C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B 1 (1067392934684306691 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry108C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (971 / 2000) (129688241564143263 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry108C_hz2 hx hc) (lowGeometry108C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (971 / 2000) (107631911345741671 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry108C_hz33 hx hc) (lowGeometry108C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (971 / 2000) (107631911345741671 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry108C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry108C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (966852897848371889 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry108C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (467402263038897123 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry108C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (226923798705384553 / 500000000000000000) (243 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry108C_hz2 hx hc) (lowGeometry108C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (434441006938633803 / 1000000000000000000) (243 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry108C_hz38 hx hc) (lowGeometry108C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry108C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (257 / 500) (1029 / 2000) θ) : B (434441006938633803 / 1000000000000000000) (243 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry108C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry108C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (257 / 500) (1029 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (203894361 / 500000000) (23006961 / 40000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64353511 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry108C_hz12 hx hc).2
  have hrp := (lowGeometry108C_hz16 hx hc).2
  have hbn := (lowGeometry108C_hz21 hx hc).2
  have hlo := (lowGeometry108C_hz40 hx hc).1
  have hhi := (lowGeometry108C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry109W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (1029 / 2000) (103 / 200) θ := hc

theorem lowGeometry109W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry109W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (97 / 200) (971 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry109W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (99813 / 400000) (100013 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry109W_hz0 hx hc) (lowGeometry109W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (100013 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry109W_hz3 hx hc) (lowGeometry109W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (698816661623419 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry109W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (2096449984870257 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry109W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (1029 / 1000) (103 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry109W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry109W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry109W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (103 / 2000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry109W_hz7 hx hc) (lowGeometry109W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (3705824984870257 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry109W_hz6 hx hc) (lowGeometry109W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (3705824984870257 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry109W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry109W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (1029 / 50) (103 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry109W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (103 / 40000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry109W_hz13 hx hc) (lowGeometry109W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (3786293734870257 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry109W_hz12 hx hc) (lowGeometry109W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (3786293734870257 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry109W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry109W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (103 / 1600000) (θ * x) := bmul (lowGeometry109W_hz0 hx hc) (lowGeometry109W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (132731958762887 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry109W_hz17 hx hc) (lowGeometry109W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (5760467836098189 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry109W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (17281403508294567 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry109W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (17281403508294567 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry109W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry109W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (1029 / 250) (103 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry109W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry109W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (4606300033649567 / 100000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry109W_hz22 hx hc) (lowGeometry109W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry109W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry109W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry109W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry109W_hz26 hx hc) (lowGeometry109W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry109W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (6052619525874727 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry109W_hz24 hx hc) (lowGeometry109W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (267281403508294567 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry109W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (1143029578581820469 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry109W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (97 / 200) (277470430200736919 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry109W_hz2 hx hc) (lowGeometry109W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (97 / 200) (301680908304235827 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry109W_hz33 hx hc) (lowGeometry109W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (97 / 200) (301680908304235827 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry109W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry109W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (232718596491705433 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry109W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (216631780612276849 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry109W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (420265654387817087 / 1000000000000000000) (971 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry109W_hz2 hx hc) (lowGeometry109W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (371844698180819271 / 1000000000000000000) (971 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry109W_hz38 hx hc) (lowGeometry109W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (371844698180819271 / 1000000000000000000) (971 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry109W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry109W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1029 / 2000) (103 / 200) θ) :
    OverlapGuard n θ lowWideWindow (13266411 / 40000000) (68453881 / 100000000) ∧ radiusMinus n θ lowWideWindow ≤ (148233 / 1250000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry109W_hz12 hx hc).2
  have hrp := (lowGeometry109W_hz16 hx hc).2
  have hbn := (lowGeometry109W_hz21 hx hc).2
  have hlo := (lowGeometry109W_hz40 hx hc).1
  have hhi := (lowGeometry109W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry109C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (1029 / 2000) (103 / 200) θ := hc

theorem lowGeometry109C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry109C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (97 / 200) (971 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry109C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (99813 / 400000) (100013 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry109C_hz0 hx hc) (lowGeometry109C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (100013 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry109C_hz3 hx hc) (lowGeometry109C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (698816661623419 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry109C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (8050367941901787 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry109C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (1029 / 1000) (103 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry109C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry109C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry109C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (8045587396983517 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry109C_hz7 hx hc) (lowGeometry109C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (2011994417360663 / 31250000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry109C_hz6 hx hc) (lowGeometry109C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (2011994417360663 / 31250000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry109C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry109C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (803649 / 100000) (80443 / 10000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry109C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (80443 / 80000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry109C_hz13 hx hc) (lowGeometry109C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (2043417464235663 / 31250000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry109C_hz12 hx hc) (lowGeometry109C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (2043417464235663 / 31250000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry109C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry109C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (103 / 1600000) (θ * x) := bmul (lowGeometry109C_hz0 hx hc) (lowGeometry109C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (132731958762887 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry109C_hz17 hx hc) (lowGeometry109C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (5760467836098189 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry109C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (33180294735925569 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry109C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (33180294735925569 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry109C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry109C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (336483 / 200000) (33681 / 20000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry109C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry109C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (9414125693771303 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry109C_hz22 hx hc) (lowGeometry109C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry109C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry109C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry109C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry109C_hz26 hx hc) (lowGeometry109C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry109C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 0 (9712725066229039 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry109C_hz24 hx hc) (lowGeometry109C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (1033180294735925569 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry109C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B 1 (1067461521430614029 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry109C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (97 / 200) (64781571081820389 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry109C_hz2 hx hc) (lowGeometry109C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (97 / 200) (53767801878702119 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry109C_hz33 hx hc) (lowGeometry109C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (97 / 200) (53767801878702119 / 100000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry109C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry109C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (966819705264074431 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry109C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (116842542810863969 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry109C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (453349066106152199 / 1000000000000000000) (971 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry109C_hz2 hx hc) (lowGeometry109C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (433923615973694121 / 1000000000000000000) (971 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry109C_hz38 hx hc) (lowGeometry109C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry109C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1029 / 2000) (103 / 200) θ) : B (433923615973694121 / 1000000000000000000) (971 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry109C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry109C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1029 / 2000) (103 / 200) θ) :
    OverlapGuard n θ lowCoreWindow (407291111 / 1000000000) (17958687 / 31250000) ∧ radiusMinus n θ lowCoreWindow ≤ (32191911 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry109C_hz12 hx hc).2
  have hrp := (lowGeometry109C_hz16 hx hc).2
  have hbn := (lowGeometry109C_hz21 hx hc).2
  have hlo := (lowGeometry109C_hz40 hx hc).1
  have hhi := (lowGeometry109C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry110W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (103 / 200) (1031 / 2000) θ := hc

theorem lowGeometry110W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry110W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (969 / 2000) (97 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry110W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (99807 / 400000) (100007 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry110W_hz0 hx hc) (lowGeometry110W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (100007 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry110W_hz3 hx hc) (lowGeometry110W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (5590365596273647 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry110W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (16771096788820941 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry110W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (103 / 100) (1031 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry110W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry110W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry110W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1031 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry110W_hz7 hx hc) (lowGeometry110W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (29658596788820941 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry110W_hz6 hx hc) (lowGeometry110W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (29658596788820941 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry110W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry110W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (103 / 5) (1031 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry110W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1031 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry110W_hz13 hx hc) (lowGeometry110W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (30302971788820941 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry110W_hz12 hx hc) (lowGeometry110W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (30302971788820941 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry110W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry110W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1031 / 16000000) (θ * x) := bmul (lowGeometry110W_hz0 hx hc) (lowGeometry110W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1039046375129 / 7812500000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry110W_hz17 hx hc) (lowGeometry110W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (11532473109290653 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry110W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (34597419327871959 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry110W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (34597419327871959 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry110W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry110W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (103 / 25) (1031 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry110W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry110W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (23053860848022833 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry110W_hz22 hx hc) (lowGeometry110W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry110W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry110W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry110W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry110W_hz26 hx hc) (lowGeometry110W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry110W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (12116991711022997 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry110W_hz24 hx hc) (lowGeometry110W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (534597419327871959 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry110W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (1143177603008082269 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry110W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (969 / 2000) (554441137458919901 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry110W_hz2 hx hc) (lowGeometry110W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (969 / 2000) (602909104303011889 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry110W_hz33 hx hc) (lowGeometry110W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (969 / 2000) (602909104303011889 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry110W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry110W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (465402580672128041 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry110W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (216599562096276649 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry110W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (83953990268516829 / 200000000000000000) (97 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry110W_hz2 hx hc) (lowGeometry110W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (371301984498492157 / 1000000000000000000) (97 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry110W_hz38 hx hc) (lowGeometry110W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (371301984498492157 / 1000000000000000000) (97 / 200) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry110W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry110W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (103 / 200) (1031 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (165580649 / 500000000) (21376951 / 31250000) ∧ radiusMinus n θ lowWideWindow ≤ (29658597 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry110W_hz12 hx hc).2
  have hrp := (lowGeometry110W_hz16 hx hc).2
  have hbn := (lowGeometry110W_hz21 hx hc).2
  have hlo := (lowGeometry110W_hz40 hx hc).1
  have hhi := (lowGeometry110W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry110C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (103 / 200) (1031 / 2000) θ := hc

theorem lowGeometry110C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry110C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (969 / 2000) (97 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry110C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (99807 / 400000) (100007 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry110C_hz0 hx hc) (lowGeometry110C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (100007 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry110C_hz3 hx hc) (lowGeometry110C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (5590365596273647 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry110C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (32200505834536207 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry110C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (103 / 100) (1031 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry110C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry110C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry110C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (8053398646883501 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry110C_hz7 hx hc) (lowGeometry110C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (64414100422070211 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry110C_hz6 hx hc) (lowGeometry110C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (64414100422070211 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry110C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry110C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (80443 / 10000) (805211 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry110C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (805211 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry110C_hz13 hx hc) (lowGeometry110C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (65420614172070211 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry110C_hz12 hx hc) (lowGeometry110C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (65420614172070211 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry110C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry110C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1031 / 16000000) (θ * x) := bmul (lowGeometry110C_hz0 hx hc) (lowGeometry110C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (1039046375129 / 7812500000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry110C_hz17 hx hc) (lowGeometry110C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (11532473109290653 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry110C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (33213522554757081 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry110C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (33213522554757081 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry110C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry110C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (33681 / 20000) (337137 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry110C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry110C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (9423265621629333 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry110C_hz22 hx hc) (lowGeometry110C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry110C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry110C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry110C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry110C_hz26 hx hc) (lowGeometry110C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry110C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 0 (4861077448195213 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry110C_hz24 hx hc) (lowGeometry110C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (1033213522554757081 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry110C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B 1 (13344127289875119 / 12500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry110C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (969 / 2000) (258876069423577309 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry110C_hz2 hx hc) (lowGeometry110C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (969 / 2000) (53719644863993547 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry110C_hz33 hx hc) (lowGeometry110C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (969 / 2000) (53719644863993547 / 100000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry110C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry110C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (966786477445242919 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry110C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (186935218594196239 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry110C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (113212641761110097 / 250000000000000000) (97 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry110C_hz2 hx hc) (lowGeometry110C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (27087891078228721 / 62500000000000000) (97 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry110C_hz38 hx hc) (lowGeometry110C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry110C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (103 / 200) (1031 / 2000) θ) : B (27087891078228721 / 62500000000000000) (97 / 200) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry110C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry110C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (103 / 200) (1031 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (406793571 / 1000000000) (574181857 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64414101 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry110C_hz12 hx hc).2
  have hrp := (lowGeometry110C_hz16 hx hc).2
  have hbn := (lowGeometry110C_hz21 hx hc).2
  have hlo := (lowGeometry110C_hz40 hx hc).1
  have hhi := (lowGeometry110C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry111W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (1031 / 2000) (129 / 250) θ := hc

theorem lowGeometry111W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry111W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (121 / 250) (969 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry111W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (124751 / 500000) (125001 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry111W_hz0 hx hc) (lowGeometry111W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (125001 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry111W_hz3 hx hc) (lowGeometry111W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (5590192304384529 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry111W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (16770576913153587 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry111W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (1031 / 1000) (129 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry111W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry111W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry111W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (129 / 2500) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry111W_hz7 hx hc) (lowGeometry111W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (29670576913153587 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry111W_hz6 hx hc) (lowGeometry111W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (29670576913153587 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry111W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry111W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (1031 / 50) (516 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry111W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (129 / 50000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry111W_hz13 hx hc) (lowGeometry111W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (30315576913153587 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry111W_hz12 hx hc) (lowGeometry111W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (30315576913153587 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry111W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry111W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (129 / 2000000) (θ * x) := bmul (lowGeometry111W_hz0 hx hc) (lowGeometry111W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (66632231404959 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry111W_hz17 hx hc) (lowGeometry111W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (11544022817454841 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry111W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (34632068452364523 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry111W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (34632068452364523 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry111W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry111W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (1031 / 250) (516 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry111W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry111W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (23076221527797831 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry111W_hz22 hx hc) (lowGeometry111W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry111W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry111W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry111W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry111W_hz26 hx hc) (lowGeometry111W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry111W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (48514977481186161 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry111W_hz24 hx hc) (lowGeometry111W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (534632068452364523 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry111W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (1143325794470615141 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry111W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (121 / 250) (138485336855253259 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry111W_hz2 hx hc) (lowGeometry111W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (121 / 250) (602456324902199197 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry111W_hz33 hx hc) (lowGeometry111W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (121 / 250) (602456324902199197 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry111W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry111W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (465367931547635477 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry111W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (216567311712924739 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry111W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (209637157738111147 / 500000000000000000) (969 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry111W_hz2 hx hc) (lowGeometry111W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (370759337995036133 / 1000000000000000000) (969 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry111W_hz38 hx hc) (lowGeometry111W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (370759337995036133 / 1000000000000000000) (969 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry111W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry111W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1031 / 2000) (129 / 250) θ) :
    OverlapGuard n θ lowWideWindow (165331223 / 500000000) (341792937 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (29670577 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry111W_hz12 hx hc).2
  have hrp := (lowGeometry111W_hz16 hx hc).2
  have hbn := (lowGeometry111W_hz21 hx hc).2
  have hlo := (lowGeometry111W_hz40 hx hc).1
  have hhi := (lowGeometry111W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry111C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (1031 / 2000) (129 / 250) θ := hc

theorem lowGeometry111C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry111C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (121 / 250) (969 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry111C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (124751 / 500000) (125001 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry111C_hz0 hx hc) (lowGeometry111C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (125001 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry111C_hz3 hx hc) (lowGeometry111C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (5590192304384529 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry111C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (4024938459156861 / 125000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry111C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (1031 / 1000) (129 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry111C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry111C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry111C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (1612241979356697 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry111C_hz7 hx hc) (lowGeometry111C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (16111086815097207 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry111C_hz6 hx hc) (lowGeometry111C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (16111086815097207 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry111C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry111C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (805211 / 100000) (100749 / 12500) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry111C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (100749 / 100000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry111C_hz13 hx hc) (lowGeometry111C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (16362959315097207 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry111C_hz12 hx hc) (lowGeometry111C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (16362959315097207 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry111C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry111C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (129 / 2000000) (θ * x) := bmul (lowGeometry111C_hz0 hx hc) (lowGeometry111C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (66632231404959 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry111C_hz17 hx hc) (lowGeometry111C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (11544022817454841 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry111C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (33246785714269943 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry111C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (33246785714269943 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry111C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry111C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (337137 / 200000) (42183 / 25000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry111C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry111C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (18864811098974727 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry111C_hz22 hx hc) (lowGeometry111C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry111C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry111C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry111C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry111C_hz26 hx hc) (lowGeometry111C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry111C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 0 (19463169453103627 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry111C_hz24 hx hc) (lowGeometry111C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (1033246785714269943 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry111C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B 1 (106759892018887047 / 100000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry111C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (121 / 250) (517251676831507743 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry111C_hz2 hx hc) (lowGeometry111C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (121 / 250) (53671484628461137 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry111C_hz33 hx hc) (lowGeometry111C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (121 / 250) (53671484628461137 / 100000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry111C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry111C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (966753214285730057 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry111C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (934611777331790697 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry111C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (452352100228586697 / 1000000000000000000) (969 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry111C_hz2 hx hc) (lowGeometry111C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (43288893077548307 / 100000000000000000) (969 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry111C_hz38 hx hc) (lowGeometry111C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry111C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1031 / 2000) (129 / 250) θ) : B (43288893077548307 / 100000000000000000) (969 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry111C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry111C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1031 / 2000) (129 / 250) θ) :
    OverlapGuard n θ lowCoreWindow (50787013 / 125000000) (143421411 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (16111087 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry111C_hz12 hx hc).2
  have hrp := (lowGeometry111C_hz16 hx hc).2
  have hbn := (lowGeometry111C_hz21 hx hc).2
  have hlo := (lowGeometry111C_hz40 hx hc).1
  have hhi := (lowGeometry111C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry112W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (129 / 250) (1033 / 2000) θ := hc

theorem lowGeometry112W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry112W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (967 / 2000) (121 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry112W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (124743 / 500000) (124993 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry112W_hz0 hx hc) (lowGeometry112W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (124993 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry112W_hz3 hx hc) (lowGeometry112W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (2795006708399821 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry112W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (8385020125199463 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry112W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (129 / 125) (1033 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry112W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry112W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry112W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1033 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry112W_hz7 hx hc) (lowGeometry112W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (14841270125199463 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry112W_hz6 hx hc) (lowGeometry112W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (14841270125199463 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry112W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry112W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (516 / 25) (1033 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry112W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1033 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry112W_hz13 hx hc) (lowGeometry112W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (15164082625199463 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry112W_hz12 hx hc) (lowGeometry112W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (15164082625199463 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry112W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry112W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1033 / 16000000) (θ * x) := bmul (lowGeometry112W_hz0 hx hc) (lowGeometry112W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (8345721302999 / 62500000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry112W_hz17 hx hc) (lowGeometry112W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (361112026051971 / 31250000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry112W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1083336078155913 / 15625000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry112W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1083336078155913 / 15625000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry112W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry112W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (516 / 125) (1033 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry112W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry112W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (23098582207572829 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry112W_hz22 hx hc) (lowGeometry112W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry112W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry112W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry112W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry112W_hz26 hx hc) (lowGeometry112W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry112W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (24280994059140167 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry112W_hz24 hx hc) (lowGeometry112W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (16708336078155913 / 15625000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry112W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (1143474153474484289 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry112W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (967 / 2000) (138360372570412599 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry112W_hz2 hx hc) (lowGeometry112W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (967 / 2000) (60200347839993073 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry112W_hz33 hx hc) (lowGeometry112W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (967 / 2000) (60200347839993073 / 100000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry112W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry112W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (14541663921844087 / 15625000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry112W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (2706687867083033 / 3125000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry112W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (83755749359017373 / 200000000000000000) (121 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry112W_hz2 hx hc) (lowGeometry112W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (370216758676806531 / 1000000000000000000) (121 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry112W_hz38 hx hc) (lowGeometry112W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (370216758676806531 / 1000000000000000000) (121 / 250) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry112W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry112W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (129 / 250) (1033 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (330163719 / 1000000000) (683109137 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (59365081 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry112W_hz12 hx hc).2
  have hrp := (lowGeometry112W_hz16 hx hc).2
  have hbn := (lowGeometry112W_hz21 hx hc).2
  have hlo := (lowGeometry112W_hz40 hx hc).1
  have hhi := (lowGeometry112W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry112C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (129 / 250) (1033 / 2000) θ := hc

theorem lowGeometry112C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry112C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (967 / 2000) (121 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry112C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (124743 / 500000) (124993 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry112C_hz0 hx hc) (lowGeometry112C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (124993 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry112C_hz3 hx hc) (lowGeometry112C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (2795006708399821 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry112C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (16099238640382969 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry112C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (129 / 125) (1033 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry112C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry112C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry112C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (8069021146683469 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry112C_hz7 hx hc) (lowGeometry112C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (32237280933749907 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry112C_hz6 hx hc) (lowGeometry112C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (32237280933749907 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry112C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry112C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (100749 / 12500) (806773 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry112C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (806773 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry112C_hz13 hx hc) (lowGeometry112C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (32741514058749907 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry112C_hz12 hx hc) (lowGeometry112C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (32741514058749907 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry112C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry112C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (1033 / 16000000) (θ * x) := bmul (lowGeometry112C_hz0 hx hc) (lowGeometry112C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (8345721302999 / 62500000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry112C_hz17 hx hc) (lowGeometry112C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (361112026051971 / 31250000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry112C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (2080005270059353 / 62500000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry112C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (2080005270059353 / 62500000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry112C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry112C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (42183 / 25000) (337791 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry112C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry112C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (4720772738672697 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry112C_hz22 hx hc) (lowGeometry112C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry112C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry112C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry112C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry112C_hz26 hx hc) (lowGeometry112C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry112C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 0 (9741014556713201 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry112C_hz24 hx hc) (lowGeometry112C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (64580005270059353 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry112C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B 1 (213533546530861763 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry112C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (967 / 2000) (516751182604685467 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry112C_hz2 hx hc) (lowGeometry112C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (967 / 2000) (536233211718111869 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry112C_hz33 hx hc) (lowGeometry112C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (967 / 2000) (536233211718111869 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry112C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry112C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (60419994729940647 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry112C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (467273697685255111 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry112C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (112963416415410423 / 250000000000000000) (121 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry112C_hz2 hx hc) (lowGeometry112C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (43237163654821529 / 100000000000000000) (121 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry112C_hz38 hx hc) (lowGeometry112C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry112C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (129 / 250) (1033 / 2000) θ) : B (43237163654821529 / 100000000000000000) (121 / 250) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry112C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry112C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (129 / 250) (1033 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (101449677 / 250000000) (17912167 / 31250000) ∧ radiusMinus n θ lowCoreWindow ≤ (32237281 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry112C_hz12 hx hc).2
  have hrp := (lowGeometry112C_hz16 hx hc).2
  have hbn := (lowGeometry112C_hz21 hx hc).2
  have hlo := (lowGeometry112C_hz40 hx hc).1
  have hhi := (lowGeometry112C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry113W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (1033 / 2000) (517 / 1000) θ := hc

theorem lowGeometry113W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry113W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (483 / 1000) (967 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry113W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (498939 / 2000000) (499939 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry113W_hz0 hx hc) (lowGeometry113W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (499939 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry113W_hz3 hx hc) (lowGeometry113W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1091763463473 / 195312500000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry113W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (3275290390419 / 48828125000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry113W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (1033 / 1000) (517 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry113W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry113W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry113W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (517 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry113W_hz7 hx hc) (lowGeometry113W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (5799704452919 / 48828125000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry113W_hz6 hx hc) (lowGeometry113W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (5799704452919 / 48828125000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry113W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry113W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (1033 / 50) (517 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry113W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (517 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry113W_hz13 hx hc) (lowGeometry113W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1481481289011 / 12207031250000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry113W_hz12 hx hc) (lowGeometry113W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1481481289011 / 12207031250000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry113W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry113W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (517 / 8000000) (θ * x) := bmul (lowGeometry113W_hz0 hx hc) (lowGeometry113W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (133799171842651 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry113W_hz17 hx hc) (lowGeometry113W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (11567159195007693 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry113W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (34701477585023079 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry113W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (34701477585023079 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry113W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry113W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (1033 / 250) (517 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry113W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry113W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (23120942887347827 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry113W_hz22 hx hc) (lowGeometry113W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry113W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry113W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry113W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry113W_hz26 hx hc) (lowGeometry113W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry113W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (48608998755374507 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry113W_hz24 hx hc) (lowGeometry113W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (534701477585023079 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry113W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (1143622680526427753 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry113W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (483 / 1000) (552941566034527819 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry113W_hz2 hx hc) (lowGeometry113W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (483 / 1000) (300775282394951163 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry113W_hz33 hx hc) (lowGeometry113W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (483 / 1000) (300775282394951163 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry113W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry113W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (465298522414976921 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry113W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (10825135748078039 / 12500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry113W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (209141622652867713 / 500000000000000000) (967 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry113W_hz2 hx hc) (lowGeometry113W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (369674246550360919 / 1000000000000000000) (967 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry113W_hz38 hx hc) (lowGeometry113W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (369674246550360919 / 1000000000000000000) (967 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry113W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry113W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1033 / 2000) (517 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (82416279 / 250000000) (682632219 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (29694487 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry113W_hz12 hx hc).2
  have hrp := (lowGeometry113W_hz16 hx hc).2
  have hbn := (lowGeometry113W_hz21 hx hc).2
  have hlo := (lowGeometry113W_hz40 hx hc).1
  have hhi := (lowGeometry113W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry113C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (1033 / 2000) (517 / 1000) θ := hc

theorem lowGeometry113C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry113C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (483 / 1000) (967 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry113C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (498939 / 2000000) (499939 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry113C_hz0 hx hc) (lowGeometry113C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (499939 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry113C_hz3 hx hc) (lowGeometry113C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (1091763463473 / 195312500000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry113C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (16098707326987469 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry113C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (1033 / 1000) (517 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry113C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry113C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry113C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (8076832396583453 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry113C_hz7 hx hc) (lowGeometry113C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (51603795392247 / 800000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry113C_hz6 hx hc) (lowGeometry113C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (51603795392247 / 800000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry113C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry113C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (806773 / 100000) (403777 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry113C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (403777 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry113C_hz13 hx hc) (lowGeometry113C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (52411349392247 / 800000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry113C_hz12 hx hc) (lowGeometry113C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (52411349392247 / 800000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry113C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry113C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (517 / 8000000) (θ * x) := bmul (lowGeometry113C_hz0 hx hc) (lowGeometry113C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (133799171842651 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry113C_hz17 hx hc) (lowGeometry113C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (11567159195007693 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry113C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (8328354620405539 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry113C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (8328354620405539 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry113C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry113C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (337791 / 200000) (169059 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry113C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry113C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (18901370810406849 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry113C_hz22 hx hc) (lowGeometry113C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry113C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry113C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry113C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry113C_hz26 hx hc) (lowGeometry113C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry113C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 0 (19500888773749177 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry113C_hz24 hx hc) (lowGeometry113C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (258328354620405539 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry113C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B 1 (1067736620814175997 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry113C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (483 / 1000) (103250131232730819 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry113C_hz2 hx hc) (lowGeometry113C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (483 / 1000) (66968943117175409 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry113C_hz33 hx hc) (lowGeometry113C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (483 / 1000) (66968943117175409 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry113C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry113C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (241671645379594461 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry113C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (233620736721921843 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry113C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (451355263346753 / 1000000000000000) (967 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry113C_hz2 hx hc) (lowGeometry113C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (431854374573003823 / 1000000000000000000) (967 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry113C_hz38 hx hc) (lowGeometry113C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry113C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1033 / 2000) (517 / 1000) θ) : B (431854374573003823 / 1000000000000000000) (967 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry113C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry113C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1033 / 2000) (517 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (50662673 / 125000000) (286346479 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12900949 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry113C_hz12 hx hc).2
  have hrp := (lowGeometry113C_hz16 hx hc).2
  have hbn := (lowGeometry113C_hz21 hx hc).2
  have hlo := (lowGeometry113C_hz40 hx hc).1
  have hhi := (lowGeometry113C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry114W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (517 / 1000) (207 / 400) θ := hc

theorem lowGeometry114W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry114W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (193 / 400) (483 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry114W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (99781 / 400000) (99981 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry114W_hz0 hx hc) (lowGeometry114W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (99981 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry114W_hz3 hx hc) (lowGeometry114W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (279481942618839 / 50000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry114W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (838445827856517 / 12500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry114W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (517 / 500) (207 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry114W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry114W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry114W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (207 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry114W_hz7 hx hc) (lowGeometry114W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1485320827856517 / 12500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry114W_hz6 hx hc) (lowGeometry114W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1485320827856517 / 12500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry114W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry114W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (517 / 25) (207 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry114W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (207 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry114W_hz13 hx hc) (lowGeometry114W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1517664577856517 / 12500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry114W_hz12 hx hc) (lowGeometry114W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1517664577856517 / 12500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry114W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry114W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (207 / 3200000) (θ * x) := bmul (lowGeometry114W_hz0 hx hc) (lowGeometry114W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (67033678756477 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry114W_hz17 hx hc) (lowGeometry114W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (5789372969349833 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry114W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (17368118908049499 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry114W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (17368118908049499 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry114W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry114W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (517 / 125) (207 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry114W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry114W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (46286607134245649 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry114W_hz22 hx hc) (lowGeometry114W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry114W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry114W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry114W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry114W_hz26 hx hc) (lowGeometry114W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry114W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (48656009392468679 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry114W_hz24 hx hc) (lowGeometry114W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (267368118908049499 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry114W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (1143771376134862337 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry114W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (193 / 400) (552441574673138509 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry114W_hz2 hx hc) (lowGeometry114W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (193 / 400) (150274396016401797 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry114W_hz33 hx hc) (lowGeometry114W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (193 / 400) (150274396016401797 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry114W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry114W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (232631881091950501 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry114W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (54117592100379397 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry114W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (26111738188433059 / 62500000000000000) (483 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry114W_hz2 hx hc) (lowGeometry114W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (73826360324492053 / 200000000000000000) (483 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry114W_hz38 hx hc) (lowGeometry114W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (73826360324492053 / 200000000000000000) (483 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry114W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry114W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (517 / 1000) (207 / 400) θ) :
    OverlapGuard n θ lowWideWindow (329166637 / 1000000000) (682155121 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (118825667 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry114W_hz12 hx hc).2
  have hrp := (lowGeometry114W_hz16 hx hc).2
  have hbn := (lowGeometry114W_hz21 hx hc).2
  have hlo := (lowGeometry114W_hz40 hx hc).1
  have hhi := (lowGeometry114W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry114C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (517 / 1000) (207 / 400) θ := hc

theorem lowGeometry114C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry114C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (193 / 400) (483 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry114C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (99781 / 400000) (99981 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry114C_hz0 hx hc) (lowGeometry114C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (99981 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry114C_hz3 hx hc) (lowGeometry114C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (279481942618839 / 50000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry114C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (32196319789690253 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry114C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (517 / 500) (207 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry114C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry114C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry114C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (8084643646483437 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry114C_hz7 hx hc) (lowGeometry114C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (64534894375624001 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry114C_hz6 hx hc) (lowGeometry114C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (64534894375624001 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry114C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry114C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (403777 / 50000) (161667 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry114C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (161667 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry114C_hz13 hx hc) (lowGeometry114C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (65545313125624001 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry114C_hz12 hx hc) (lowGeometry114C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (65545313125624001 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry114C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry114C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (207 / 3200000) (θ * x) := bmul (lowGeometry114C_hz0 hx hc) (lowGeometry114C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (67033678756477 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry114C_hz17 hx hc) (lowGeometry114C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (5789372969349833 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry114C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (33346788303455039 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry114C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (33346788303455039 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry114C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry114C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (169059 / 100000) (67689 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry114C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry114C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (18919650666122909 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry114C_hz22 hx hc) (lowGeometry114C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry114C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry114C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry114C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry114C_hz26 hx hc) (lowGeometry114C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry114C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 0 (19519748434071951 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry114C_hz24 hx hc) (lowGeometry114C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (1033346788303455039 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry114C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B 1 (266951396224266381 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry114C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (193 / 400) (515750097505282649 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry114C_hz2 hx hc) (lowGeometry114C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (193 / 400) (2676349229696773 / 5000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry114C_hz33 hx hc) (lowGeometry114C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (193 / 400) (2676349229696773 / 5000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry114C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry114C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (966653211696544961 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry114C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (934418431683245367 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry114C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (450856893287165889 / 1000000000000000000) (483 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry114C_hz2 hx hc) (lowGeometry114C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (215668572426546969 / 500000000000000000) (483 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry114C_hz38 hx hc) (lowGeometry114C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry114C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (517 / 1000) (207 / 400) θ) : B (215668572426546969 / 500000000000000000) (483 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry114C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry114C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (517 / 1000) (207 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (404804131 / 1000000000) (286098243 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12906979 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry114C_hz12 hx hc).2
  have hrp := (lowGeometry114C_hz16 hx hc).2
  have hbn := (lowGeometry114C_hz21 hx hc).2
  have hlo := (lowGeometry114C_hz40 hx hc).1
  have hhi := (lowGeometry114C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry115W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (207 / 400) (259 / 500) θ := hc

theorem lowGeometry115W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry115W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (241 / 500) (193 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry115W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (49887 / 200000) (49987 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry115W_hz0 hx hc) (lowGeometry115W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (49987 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry115W_hz3 hx hc) (lowGeometry115W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (5589443174413709 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry115W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (16768329523241127 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry115W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (207 / 200) (259 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry115W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry115W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry115W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (259 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry115W_hz7 hx hc) (lowGeometry115W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (29718329523241127 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry115W_hz6 hx hc) (lowGeometry115W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (29718329523241127 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry115W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry115W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (207 / 10) (518 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry115W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (259 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry115W_hz13 hx hc) (lowGeometry115W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (30365829523241127 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry115W_hz12 hx hc) (lowGeometry115W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (30365829523241127 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry115W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry115W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (259 / 4000000) (θ * x) := bmul (lowGeometry115W_hz0 hx hc) (lowGeometry115W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (134336099585063 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry115W_hz17 hx hc) (lowGeometry115W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (1448793137758669 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry115W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (4346379413276007 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry115W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (4346379413276007 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry115W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry115W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (207 / 50) (518 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry115W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry115W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (9266265698759129 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry115W_hz22 hx hc) (lowGeometry115W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry115W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry115W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry115W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry115W_hz26 hx hc) (lowGeometry115W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry115W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (12175755007390713 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry115W_hz24 hx hc) (lowGeometry115W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (66846379413276007 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry115W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (1143920240809894493 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry115W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (241 / 500) (551941516190774093 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry115W_hz2 hx hc) (lowGeometry115W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (241 / 500) (120128907244067389 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry115W_hz33 hx hc) (lowGeometry115W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (241 / 500) (120128907244067389 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry115W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry115W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (58153620586723993 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry115W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (216437989590057511 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry115W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (417292443929630881 / 1000000000000000000) (193 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry115W_hz2 hx hc) (lowGeometry115W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (368589423900068029 / 1000000000000000000) (193 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry115W_hz38 hx hc) (lowGeometry115W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (368589423900068029 / 1000000000000000000) (193 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry115W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry115W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (207 / 400) (259 / 500) θ) :
    OverlapGuard n θ lowWideWindow (328668283 / 1000000000) (170419461 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (118873319 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry115W_hz12 hx hc).2
  have hrp := (lowGeometry115W_hz16 hx hc).2
  have hbn := (lowGeometry115W_hz21 hx hc).2
  have hlo := (lowGeometry115W_hz40 hx hc).1
  have hhi := (lowGeometry115W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry115C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (207 / 400) (259 / 500) θ := hc

theorem lowGeometry115C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry115C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (241 / 500) (193 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry115C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (49887 / 200000) (49987 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry115C_hz0 hx hc) (lowGeometry115C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (49987 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry115C_hz3 hx hc) (lowGeometry115C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (5589443174413709 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry115C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (8048798171155741 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry115C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (207 / 200) (259 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry115C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry115C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry115C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (8092454896383421 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry115C_hz7 hx hc) (lowGeometry115C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (8070626533769581 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry115C_hz6 hx hc) (lowGeometry115C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (8070626533769581 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry115C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry115C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (161667 / 20000) (202279 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry115C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (202279 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry115C_hz13 hx hc) (lowGeometry115C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (8197050908769581 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry115C_hz12 hx hc) (lowGeometry115C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (8197050908769581 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry115C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry115C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (259 / 4000000) (θ * x) := bmul (lowGeometry115C_hz0 hx hc) (lowGeometry115C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (134336099585063 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry115C_hz17 hx hc) (lowGeometry115C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (1448793137758669 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry115C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (16690096946979867 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry115C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (16690096946979867 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry115C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry115C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (67689 / 40000) (84693 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry115C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry115C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (1893793052183897 / 100000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry115C_hz22 hx hc) (lowGeometry115C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry115C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry115C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry115C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry115C_hz26 hx hc) (lowGeometry115C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry115C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 0 (9769304047197363 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry115C_hz24 hx hc) (lowGeometry115C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (516690096946979867 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry115C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B 1 (213574925026463563 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry115C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (241 / 500) (257624753313171673 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry115C_hz2 hx hc) (lowGeometry115C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (241 / 500) (66848514340092259 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry115C_hz33 hx hc) (lowGeometry115C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (241 / 500) (66848514340092259 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry115C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry115C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (483309903053020133 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry115C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (467176924778239439 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry115C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (450358555486222819 / 1000000000000000000) (193 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry115C_hz2 hx hc) (lowGeometry115C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (430819947391828093 / 1000000000000000000) (193 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry115C_hz38 hx hc) (lowGeometry115C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry115C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (207 / 400) (259 / 500) θ) : B (430819947391828093 / 1000000000000000000) (193 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry115C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry115C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (207 / 400) (259 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (8086139 / 20000000) (71462491 / 125000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64565013 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry115C_hz12 hx hc).2
  have hrp := (lowGeometry115C_hz16 hx hc).2
  have hbn := (lowGeometry115C_hz21 hx hc).2
  have hlo := (lowGeometry115C_hz40 hx hc).1
  have hhi := (lowGeometry115C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry116W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (259 / 500) (1037 / 2000) θ := hc

theorem lowGeometry116W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry116W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (963 / 2000) (241 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry116W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (249417 / 1000000) (249917 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry116W_hz0 hx hc) (lowGeometry116W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (249917 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry116W_hz3 hx hc) (lowGeometry116W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (5589241898504663 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry116W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (16767725695513989 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry116W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (259 / 250) (1037 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry116W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry116W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry116W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1037 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry116W_hz7 hx hc) (lowGeometry116W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (29730225695513989 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry116W_hz6 hx hc) (lowGeometry116W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (29730225695513989 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry116W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry116W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (518 / 25) (1037 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry116W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1037 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry116W_hz13 hx hc) (lowGeometry116W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (30378350695513989 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry116W_hz12 hx hc) (lowGeometry116W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (30378350695513989 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry116W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry116W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1037 / 16000000) (θ * x) := bmul (lowGeometry116W_hz0 hx hc) (lowGeometry116W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (33651349948079 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry116W_hz17 hx hc) (lowGeometry116W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (11601956722566931 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry116W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (34805870167700793 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry116W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (34805870167700793 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry116W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry116W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (518 / 125) (1037 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry116W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry116W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (46376049853345641 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry116W_hz22 hx hc) (lowGeometry116W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry116W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry116W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry116W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry116W_hz26 hx hc) (lowGeometry116W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry116W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (190429807291629 / 3906250000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry116W_hz24 hx hc) (lowGeometry116W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (534805870167700793 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry116W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (1144069275063326549 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry116W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (963 / 2000) (551441390580523397 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry116W_hz2 hx hc) (lowGeometry116W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (963 / 2000) (600191421247180421 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry116W_hz33 hx hc) (lowGeometry116W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (963 / 2000) (600191421247180421 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry116W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry116W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (465194129832299207 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry116W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (216405578430430051 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry116W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (208398572028504139 / 500000000000000000) (241 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry116W_hz2 hx hc) (lowGeometry116W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (184023556695175627 / 500000000000000000) (241 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry116W_hz38 hx hc) (lowGeometry116W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (184023556695175627 / 500000000000000000) (241 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry116W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry116W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (259 / 500) (1037 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (328170053 / 1000000000) (681200387 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (118920903 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry116W_hz12 hx hc).2
  have hrp := (lowGeometry116W_hz16 hx hc).2
  have hbn := (lowGeometry116W_hz21 hx hc).2
  have hlo := (lowGeometry116W_hz40 hx hc).1
  have hhi := (lowGeometry116W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry116C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (259 / 500) (1037 / 2000) θ := hc

theorem lowGeometry116C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry116C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (963 / 2000) (241 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry116C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (249417 / 1000000) (249917 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry116C_hz0 hx hc) (lowGeometry116C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (249917 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry116C_hz3 hx hc) (lowGeometry116C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (5589241898504663 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry116C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (32194033335386859 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry116C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (259 / 250) (1037 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry116C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry116C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry116C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1620053229256681 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry116C_hz7 hx hc) (lowGeometry116C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (64595097920520479 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry116C_hz6 hx hc) (lowGeometry116C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (64595097920520479 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry116C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry116C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (202279 / 25000) (809897 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry116C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (809897 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry116C_hz13 hx hc) (lowGeometry116C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (65607469170520479 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry116C_hz12 hx hc) (lowGeometry116C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (65607469170520479 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry116C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry116C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (1037 / 16000000) (θ * x) := bmul (lowGeometry116C_hz0 hx hc) (lowGeometry116C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (33651349948079 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry116C_hz17 hx hc) (lowGeometry116C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (11601956722566931 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry116C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (16706817680496381 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry116C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (16706817680496381 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry116C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry116C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (84693 / 50000) (339099 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry116C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry116C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (18956210377555031 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry116C_hz22 hx hc) (lowGeometry116C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry116C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry116C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry116C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry116C_hz26 hx hc) (lowGeometry116C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry116C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 0 (19557467754717501 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry116C_hz24 hx hc) (lowGeometry116C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (516706817680496381 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry116C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B 1 (106794374175002291 / 100000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry116C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (963 / 2000) (514748883523511043 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry116C_hz2 hx hc) (lowGeometry116C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (963 / 2000) (8348536738722321 / 15625000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry116C_hz33 hx hc) (lowGeometry116C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (963 / 2000) (8348536738722321 / 15625000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry116C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry116C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (483293182319503619 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry116C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (934289200306051861 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry116C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (449860249947363971 / 1000000000000000000) (241 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry116C_hz2 hx hc) (lowGeometry116C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (43030278219264647 / 100000000000000000) (241 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry116C_hz38 hx hc) (lowGeometry116C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry116C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (259 / 500) (1037 / 2000) θ) : B (43030278219264647 / 100000000000000000) (241 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry116C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry116C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (259 / 500) (1037 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (5047623 / 12500000) (142800821 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32297549 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry116C_hz12 hx hc).2
  have hrp := (lowGeometry116C_hz16 hx hc).2
  have hbn := (lowGeometry116C_hz21 hx hc).2
  have hlo := (lowGeometry116C_hz40 hx hc).1
  have hhi := (lowGeometry116C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry117W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (1037 / 2000) (519 / 1000) θ := hc

theorem lowGeometry117W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry117W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (481 / 1000) (963 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry117W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (498797 / 2000000) (499797 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry117W_hz0 hx hc) (lowGeometry117W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (499797 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry117W_hz3 hx hc) (lowGeometry117W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (5589035024044849 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry117W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (16767105072134547 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry117W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (1037 / 1000) (519 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry117W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry117W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry117W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (519 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry117W_hz7 hx hc) (lowGeometry117W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (29742105072134547 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry117W_hz6 hx hc) (lowGeometry117W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (29742105072134547 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry117W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry117W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (1037 / 50) (519 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry117W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (519 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry117W_hz13 hx hc) (lowGeometry117W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (30390855072134547 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry117W_hz12 hx hc) (lowGeometry117W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (30390855072134547 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry117W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry117W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (519 / 8000000) (θ * x) := bmul (lowGeometry117W_hz0 hx hc) (lowGeometry117W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (6743762993763 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry117W_hz17 hx hc) (lowGeometry117W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (464543233510527 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry117W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (1393629700531581 / 20000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry117W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (1393629700531581 / 20000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry117W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry117W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (1037 / 250) (519 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry117W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry117W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (46420771212895637 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry117W_hz22 hx hc) (lowGeometry117W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry117W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry117W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry117W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry117W_hz26 hx hc) (lowGeometry117W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry117W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (48797041303751197 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry117W_hz24 hx hc) (lowGeometry117W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (21393629700531581 / 20000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry117W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (1144218479408667461 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry117W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (481 / 1000) (550941197835273383 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry117W_hz2 hx hc) (lowGeometry117W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (481 / 1000) (29986911956951229 / 50000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry117W_hz33 hx hc) (lowGeometry117W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (481 / 1000) (29986911956951229 / 50000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry117W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry117W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (18606370299468419 / 20000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry117W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (43274626965117563 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry117W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (104075477851107739 / 250000000000000000) (963 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry117W_hz2 hx hc) (lowGeometry117W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (367504870100679759 / 1000000000000000000) (963 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry117W_hz38 hx hc) (lowGeometry117W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (367504870100679759 / 1000000000000000000) (963 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry117W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry117W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1037 / 2000) (519 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (327671947 / 1000000000) (2722891 / 4000000) ∧ radiusMinus n θ lowWideWindow ≤ (118968421 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry117W_hz12 hx hc).2
  have hrp := (lowGeometry117W_hz16 hx hc).2
  have hbn := (lowGeometry117W_hz21 hx hc).2
  have hlo := (lowGeometry117W_hz40 hx hc).1
  have hhi := (lowGeometry117W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry117C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (1037 / 2000) (519 / 1000) θ := hc

theorem lowGeometry117C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry117C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (481 / 1000) (963 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry117C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (498797 / 2000000) (499797 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry117C_hz0 hx hc) (lowGeometry117C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (499797 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry117C_hz3 hx hc) (lowGeometry117C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (5589035024044849 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry117C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (32192841738498331 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry117C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (1037 / 1000) (519 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry117C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry117C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry117C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (8108077396183389 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry117C_hz7 hx hc) (lowGeometry117C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (64625151323231887 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry117C_hz6 hx hc) (lowGeometry117C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (64625151323231887 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry117C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry117C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (809897 / 100000) (405339 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry117C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (405339 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry117C_hz13 hx hc) (lowGeometry117C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (65638498823231887 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry117C_hz12 hx hc) (lowGeometry117C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (65638498823231887 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry117C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry117C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (519 / 8000000) (θ * x) := bmul (lowGeometry117C_hz0 hx hc) (lowGeometry117C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (6743762993763 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry117C_hz17 hx hc) (lowGeometry117C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (464543233510527 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry117C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (4180889101594743 / 125000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry117C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (4180889101594743 / 125000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry117C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry117C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (339099 / 200000) (169713 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry117C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry117C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (4743622558317773 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry117C_hz22 hx hc) (lowGeometry117C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry117C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry117C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry117C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry117C_hz26 hx hc) (lowGeometry117C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry117C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 0 (4894081853760069 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry117C_hz24 hx hc) (lowGeometry117C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (129180889101594743 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry117C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B 1 (213602586996205049 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry117C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (481 / 1000) (64281028524170457 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry117C_hz2 hx hc) (lowGeometry117C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (481 / 1000) (133456138902100983 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry117C_hz33 hx hc) (lowGeometry117C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (481 / 1000) (133456138902100983 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry117C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry117C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (120819110898405257 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry117C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (233556120932498367 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry117C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (224680988337063429 / 500000000000000000) (963 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry117C_hz2 hx hc) (lowGeometry117C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (214892824629543291 / 500000000000000000) (963 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry117C_hz38 hx hc) (lowGeometry117C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry117C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1037 / 2000) (519 / 1000) θ) : B (214892824629543291 / 500000000000000000) (963 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry117C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry117C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1037 / 2000) (519 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (201656401 / 500000000) (570706553 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (126221 / 1953125) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry117C_hz12 hx hc).2
  have hrp := (lowGeometry117C_hz16 hx hc).2
  have hbn := (lowGeometry117C_hz21 hx hc).2
  have hlo := (lowGeometry117C_hz40 hx hc).1
  have hhi := (lowGeometry117C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry118W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (519 / 1000) (1039 / 2000) θ := hc

theorem lowGeometry118W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry118W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (961 / 2000) (481 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry118W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (498759 / 2000000) (499759 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry118W_hz0 hx hc) (lowGeometry118W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (499759 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry118W_hz3 hx hc) (lowGeometry118W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1117764510082513 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry118W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (3353293530247539 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry118W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (519 / 500) (1039 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry118W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry118W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry118W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1039 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry118W_hz7 hx hc) (lowGeometry118W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (5950793530247539 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry118W_hz6 hx hc) (lowGeometry118W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (5950793530247539 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry118W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry118W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (519 / 25) (1039 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry118W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1039 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry118W_hz13 hx hc) (lowGeometry118W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (6080668530247539 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry118W_hz12 hx hc) (lowGeometry118W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (6080668530247539 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry118W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry118W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1039 / 16000000) (θ * x) := bmul (lowGeometry118W_hz0 hx hc) (lowGeometry118W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (67572840790843 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry118W_hz17 hx hc) (lowGeometry118W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (11625217485349941 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry118W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (34875652456049823 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry118W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (34875652456049823 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry118W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry118W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (519 / 125) (1039 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry118W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry118W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (46465492572445633 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry118W_hz22 hx hc) (lowGeometry118W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry118W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry118W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry118W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry118W_hz26 hx hc) (lowGeometry118W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry118W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (4884405194084537 / 100000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry118W_hz24 hx hc) (lowGeometry118W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (534875652456049823 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry118W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (1144367854361139989 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry118W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (961 / 2000) (110088187589541667 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry118W_hz2 hx hc) (lowGeometry118W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (961 / 2000) (119856997977710741 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry118W_hz33 hx hc) (lowGeometry118W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (961 / 2000) (119856997977710741 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry118W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry118W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (465124347543950177 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry118W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (216340658678185351 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry118W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (103951686494868061 / 250000000000000000) (481 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry118W_hz2 hx hc) (lowGeometry118W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (183481347019313437 / 500000000000000000) (481 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry118W_hz38 hx hc) (lowGeometry118W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (183481347019313437 / 500000000000000000) (481 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry118W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry118W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (519 / 1000) (1039 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (65434793 / 200000000) (680244933 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (119015871 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry118W_hz12 hx hc).2
  have hrp := (lowGeometry118W_hz16 hx hc).2
  have hbn := (lowGeometry118W_hz21 hx hc).2
  have hlo := (lowGeometry118W_hz40 hx hc).1
  have hhi := (lowGeometry118W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry118C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (519 / 1000) (1039 / 2000) θ := hc

theorem lowGeometry118C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry118C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (961 / 2000) (481 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry118C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (498759 / 2000000) (499759 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry118C_hz0 hx hc) (lowGeometry118C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (499759 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry118C_hz3 hx hc) (lowGeometry118C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1117764510082513 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry118C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (257532943123011 / 8000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry118C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (519 / 500) (1039 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry118C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry118C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry118C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (8115888646083373 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry118C_hz7 hx hc) (lowGeometry118C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (64655172474709867 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry118C_hz6 hx hc) (lowGeometry118C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (64655172474709867 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry118C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry118C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (405339 / 50000) (811459 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry118C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (811459 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry118C_hz13 hx hc) (lowGeometry118C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (65669496224709867 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry118C_hz12 hx hc) (lowGeometry118C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (65669496224709867 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry118C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry118C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (1039 / 16000000) (θ * x) := bmul (lowGeometry118C_hz0 hx hc) (lowGeometry118C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (67572840790843 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry118C_hz17 hx hc) (lowGeometry118C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (11625217485349941 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry118C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (33480626357807831 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry118C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (33480626357807831 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry118C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry118C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (169713 / 100000) (339753 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry118C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry118C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (18992770088987153 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry118C_hz22 hx hc) (lowGeometry118C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry118C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry118C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry118C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry118C_hz26 hx hc) (lowGeometry118C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry118C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 0 (19595187075363051 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry118C_hz24 hx hc) (lowGeometry118C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (1033480626357807831 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry118C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B 1 (1068082205056926799 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry118C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (961 / 2000) (513747540632381791 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry118C_hz2 hx hc) (lowGeometry118C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (961 / 2000) (266671363853872421 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry118C_hz33 hx hc) (lowGeometry118C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (961 / 2000) (266671363853872421 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry118C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry118C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (966519373642192169 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry118C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (467079849812847737 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry118C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (17954549426805867 / 40000000000000000) (481 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry118C_hz2 hx hc) (lowGeometry118C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (53658568574347953 / 125000000000000000) (481 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry118C_hz38 hx hc) (lowGeometry118C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry118C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (519 / 1000) (1039 / 2000) θ) : B (53658568574347953 / 125000000000000000) (481 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry118C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry118C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (519 / 1000) (1039 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (80563167 / 200000000) (570209737 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64655173 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry118C_hz12 hx hc).2
  have hrp := (lowGeometry118C_hz16 hx hc).2
  have hbn := (lowGeometry118C_hz21 hx hc).2
  have hlo := (lowGeometry118C_hz40 hx hc).1
  have hhi := (lowGeometry118C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry119W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (1039 / 2000) (13 / 25) θ := hc

theorem lowGeometry119W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry119W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (12 / 25) (961 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry119W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (3117 / 12500) (12493 / 50000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry119W_hz0 hx hc) (lowGeometry119W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (12493 / 400000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry119W_hz3 hx hc) (lowGeometry119W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (174643889905287 / 31250000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry119W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (523931669715861 / 7812500000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry119W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (1039 / 1000) (26 / 25) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry119W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry119W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry119W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (13 / 250) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry119W_hz7 hx hc) (lowGeometry119W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (930181669715861 / 7812500000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry119W_hz6 hx hc) (lowGeometry119W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (930181669715861 / 7812500000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry119W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry119W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (1039 / 50) (104 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry119W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (13 / 5000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry119W_hz13 hx hc) (lowGeometry119W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (950494169715861 / 7812500000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry119W_hz12 hx hc) (lowGeometry119W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (950494169715861 / 7812500000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry119W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry119W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (13 / 200000) (θ * x) := bmul (lowGeometry119W_hz0 hx hc) (lowGeometry119W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (135416666666667 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry119W_hz17 hx hc) (lowGeometry119W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (11636866703140799 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry119W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (34910600109422397 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry119W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (34910600109422397 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry119W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry119W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (1039 / 250) (104 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry119W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry119W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (11627553482998907 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry119W_hz22 hx hc) (lowGeometry119W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry119W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry119W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry119W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry119W_hz26 hx hc) (lowGeometry119W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry119W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (24445531288969771 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry119W_hz24 hx hc) (lowGeometry119W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (534910600109422397 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry119W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (1144517400437689601 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry119W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (12 / 25) (274970305455154927 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry119W_hz2 hx hc) (lowGeometry119W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (12 / 25) (149707918372062349 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry119W_hz33 hx hc) (lowGeometry119W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (12 / 25) (149707918372062349 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry119W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry119W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (465089399890577603 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry119W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (108154074945288803 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry119W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (415311647789909003 / 1000000000000000000) (961 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry119W_hz2 hx hc) (lowGeometry119W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (366420585211969461 / 1000000000000000000) (961 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry119W_hz38 hx hc) (lowGeometry119W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (366420585211969461 / 1000000000000000000) (961 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry119W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry119W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1039 / 2000) (13 / 25) θ) :
    OverlapGuard n θ lowWideWindow (326676107 / 1000000000) (679766937 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (59531627 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry119W_hz12 hx hc).2
  have hrp := (lowGeometry119W_hz16 hx hc).2
  have hbn := (lowGeometry119W_hz21 hx hc).2
  have hlo := (lowGeometry119W_hz40 hx hc).1
  have hhi := (lowGeometry119W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry119C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (1039 / 2000) (13 / 25) θ := hc

theorem lowGeometry119C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry119C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (12 / 25) (961 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry119C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (3117 / 12500) (12493 / 50000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry119C_hz0 hx hc) (lowGeometry119C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (12493 / 400000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry119C_hz3 hx hc) (lowGeometry119C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (174643889905287 / 31250000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry119C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (12876144714937 / 400000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry119C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (1039 / 1000) (26 / 25) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry119C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry119C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry119C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (8123699895983357 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry119C_hz7 hx hc) (lowGeometry119C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (8085645171409491 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry119C_hz6 hx hc) (lowGeometry119C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (8085645171409491 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry119C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry119C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (811459 / 100000) (10153 / 1250) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry119C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (10153 / 10000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry119C_hz13 hx hc) (lowGeometry119C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (8212557671409491 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry119C_hz12 hx hc) (lowGeometry119C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (8212557671409491 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry119C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry119C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (13 / 200000) (θ * x) := bmul (lowGeometry119C_hz0 hx hc) (lowGeometry119C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (135416666666667 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry119C_hz17 hx hc) (lowGeometry119C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (11636866703140799 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry119C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (16757088052522751 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry119C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (16757088052522751 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry119C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry119C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (339753 / 200000) (4251 / 2500) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry119C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry119C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (19011049944703213 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry119C_hz22 hx hc) (lowGeometry119C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry119C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry119C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry119C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry119C_hz26 hx hc) (lowGeometry119C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry119C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 0 (784561869427433 / 40000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry119C_hz24 hx hc) (lowGeometry119C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (516757088052522751 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry119C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B 1 (1068151552210091007 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry119C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (12 / 25) (513246820836948729 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry119C_hz2 hx hc) (lowGeometry119C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (12 / 25) (266430433786317277 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry119C_hz33 hx hc) (lowGeometry119C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (12 / 25) (266430433786317277 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry119C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry119C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (483242911947477249 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry119C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (467047423894954499 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry119C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (448365526939156319 / 1000000000000000000) (961 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry119C_hz2 hx hc) (lowGeometry119C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (214375740101735247 / 500000000000000000) (961 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry119C_hz38 hx hc) (lowGeometry119C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry119C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1039 / 2000) (13 / 25) θ) : B (214375740101735247 / 500000000000000000) (961 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry119C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry119C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1039 / 2000) (13 / 25) θ) :
    OverlapGuard n θ lowCoreWindow (20115947 / 50000000) (113942567 / 200000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32342581 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry119C_hz12 hx hc).2
  have hrp := (lowGeometry119C_hz16 hx hc).2
  have hbn := (lowGeometry119C_hz21 hx hc).2
  have hlo := (lowGeometry119C_hz40 hx hc).1
  have hhi := (lowGeometry119C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry120W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (13 / 25) (1041 / 2000) θ := hc

theorem lowGeometry120W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry120W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (959 / 2000) (12 / 25) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (12467 / 50000) (3123 / 12500) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry120W_hz0 hx hc) (lowGeometry120W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (3123 / 100000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry120W_hz3 hx hc) (lowGeometry120W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1397095200764787 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry120W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (4191285602294361 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry120W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (26 / 25) (1041 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry120W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry120W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry120W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1041 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry120W_hz7 hx hc) (lowGeometry120W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (7444410602294361 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry120W_hz6 hx hc) (lowGeometry120W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (7444410602294361 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry120W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry120W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (104 / 5) (1041 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry120W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1041 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry120W_hz13 hx hc) (lowGeometry120W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (7607066852294361 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry120W_hz12 hx hc) (lowGeometry120W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (7607066852294361 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry120W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry120W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1041 / 16000000) (θ * x) := bmul (lowGeometry120W_hz0 hx hc) (lowGeometry120W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (135688216892597 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry120W_hz17 hx hc) (lowGeometry120W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1456066066133961 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry120W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (4368198198401883 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry120W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (4368198198401883 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry120W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry120W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (104 / 25) (1041 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry120W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry120W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (5819366911443203 / 125000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry120W_hz22 hx hc) (lowGeometry120W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry120W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry120W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry120W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry120W_hz26 hx hc) (lowGeometry120W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry120W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (9787614643006743 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry120W_hz24 hx hc) (lowGeometry120W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (66868198198401883 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry120W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (1144667118156993749 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry120W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (959 / 2000) (549440216715357 / 1000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry120W_hz2 hx hc) (lowGeometry120W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (959 / 2000) (119675657986078143 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry120W_hz33 hx hc) (lowGeometry120W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (959 / 2000) (119675657986078143 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry120W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry120W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (58131801801598117 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry120W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (216275608364818309 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry120W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (103704154210930379 / 250000000000000000) (12 / 25) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry120W_hz2 hx hc) (lowGeometry120W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (365878543628687801 / 1000000000000000000) (12 / 25) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry120W_hz38 hx hc) (lowGeometry120W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (365878543628687801 / 1000000000000000000) (12 / 25) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry120W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry120W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (13 / 25) (1041 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (81544593 / 250000000) (339644381 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (11911057 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry120W_hz12 hx hc).2
  have hrp := (lowGeometry120W_hz16 hx hc).2
  have hbn := (lowGeometry120W_hz21 hx hc).2
  have hlo := (lowGeometry120W_hz40 hx hc).1
  have hhi := (lowGeometry120W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry120C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (13 / 25) (1041 / 2000) θ := hc

theorem lowGeometry120C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry120C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (959 / 2000) (12 / 25) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (12467 / 50000) (3123 / 12500) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry120C_hz0 hx hc) (lowGeometry120C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (3123 / 100000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry120C_hz3 hx hc) (lowGeometry120C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1397095200764787 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry120C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (32189073425620693 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry120C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (26 / 25) (1041 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry120C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry120C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry120C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (8131511145883341 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry120C_hz7 hx hc) (lowGeometry120C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (64715118009154057 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry120C_hz6 hx hc) (lowGeometry120C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (64715118009154057 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry120C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry120C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (10153 / 1250) (813021 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry120C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (813021 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry120C_hz13 hx hc) (lowGeometry120C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (65731394259154057 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry120C_hz12 hx hc) (lowGeometry120C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (65731394259154057 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry120C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry120C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1041 / 16000000) (θ * x) := bmul (lowGeometry120C_hz0 hx hc) (lowGeometry120C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (135688216892597 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry120C_hz17 hx hc) (lowGeometry120C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (1456066066133961 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry120C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (16773881081863231 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry120C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (16773881081863231 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry120C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry120C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (4251 / 2500) (340407 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry120C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry120C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (9514664900209637 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry120C_hz22 hx hc) (lowGeometry120C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry120C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry120C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry120C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry120C_hz26 hx hc) (lowGeometry120C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry120C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 0 (98164531980043 / 5000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry120C_hz24 hx hc) (lowGeometry120C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (516773881081863231 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry120C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B 1 (1068220976673646881 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry120C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (959 / 2000) (512746068803350503 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry120C_hz2 hx hc) (lowGeometry120C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (959 / 2000) (532378975199359103 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry120C_hz33 hx hc) (lowGeometry120C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (959 / 2000) (532378975199359103 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry120C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry120C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (483226118918136769 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry120C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (116753741002342629 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry120C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (111966837621246581 / 250000000000000000) (12 / 25) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry120C_hz2 hx hc) (lowGeometry120C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (107058611022244431 / 250000000000000000) (12 / 25) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry120C_hz38 hx hc) (lowGeometry120C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry120C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (1041 / 2000) θ) : B (107058611022244431 / 250000000000000000) (12 / 25) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry120C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry120C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (13 / 25) (1041 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (100455529 / 250000000) (284607923 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64715119 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry120C_hz12 hx hc).2
  have hrp := (lowGeometry120C_hz16 hx hc).2
  have hbn := (lowGeometry120C_hz21 hx hc).2
  have hlo := (lowGeometry120C_hz40 hx hc).1
  have hhi := (lowGeometry120C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry121W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (1041 / 2000) (521 / 1000) θ := hc

theorem lowGeometry121W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry121W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (479 / 1000) (959 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry121W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (498639 / 2000000) (499639 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry121W_hz0 hx hc) (lowGeometry121W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (499639 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry121W_hz3 hx hc) (lowGeometry121W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (1397037882002489 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry121W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (4191113646007467 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry121W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (1041 / 1000) (521 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry121W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry121W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry121W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (521 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry121W_hz7 hx hc) (lowGeometry121W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (7447363646007467 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry121W_hz6 hx hc) (lowGeometry121W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (7447363646007467 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry121W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry121W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (1041 / 50) (521 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry121W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (521 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry121W_hz13 hx hc) (lowGeometry121W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (7610176146007467 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry121W_hz12 hx hc) (lowGeometry121W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (7610176146007467 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry121W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry121W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (521 / 8000000) (θ * x) := bmul (lowGeometry121W_hz0 hx hc) (lowGeometry121W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (33990083507307 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry121W_hz17 hx hc) (lowGeometry121W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (291505075030037 / 25000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry121W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (874515225090111 / 12500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry121W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (874515225090111 / 12500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry121W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry121W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (1041 / 250) (521 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry121W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry121W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (2329982832554781 / 50000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry121W_hz22 hx hc) (lowGeometry121W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry121W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry121W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry121W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry121W_hz26 hx hc) (lowGeometry121W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry121W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (3061567740757993 / 62500000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry121W_hz24 hx hc) (lowGeometry121W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (13374515225090111 / 12500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry121W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (1144817008039469969 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry121W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (479 / 1000) (548939755354925851 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry121W_hz2 hx hc) (lowGeometry121W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (479 / 1000) (597924839207053739 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry121W_hz33 hx hc) (lowGeometry121W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (479 / 1000) (597924839207053739 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry121W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry121W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (11625484774909889 / 12500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry121W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (54060758500664653 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry121W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (4143216531490939 / 10000000000000000) (959 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry121W_hz2 hx hc) (lowGeometry121W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (91334142324241503 / 250000000000000000) (959 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry121W_hz38 hx hc) (lowGeometry121W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (91334142324241503 / 250000000000000000) (959 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry121W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry121W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1041 / 2000) (521 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (325680761 / 1000000000) (678810407 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (119157819 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry121W_hz12 hx hc).2
  have hrp := (lowGeometry121W_hz16 hx hc).2
  have hbn := (lowGeometry121W_hz21 hx hc).2
  have hlo := (lowGeometry121W_hz40 hx hc).1
  have hhi := (lowGeometry121W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry121C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (1041 / 2000) (521 / 1000) θ := hc

theorem lowGeometry121C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry121C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (479 / 1000) (959 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry121C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (498639 / 2000000) (499639 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry121C_hz0 hx hc) (lowGeometry121C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (499639 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry121C_hz3 hx hc) (lowGeometry121C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (1397037882002489 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry121C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (32187752801337347 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry121C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (1041 / 1000) (521 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry121C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry121C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry121C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (325572895831333 / 10000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry121C_hz7 hx hc) (lowGeometry121C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (64745042384470647 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry121C_hz6 hx hc) (lowGeometry121C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (64745042384470647 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry121C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry121C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (813021 / 100000) (406901 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry121C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (406901 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry121C_hz13 hx hc) (lowGeometry121C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (65762294884470647 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry121C_hz12 hx hc) (lowGeometry121C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (65762294884470647 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry121C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry121C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (521 / 8000000) (θ * x) := bmul (lowGeometry121C_hz0 hx hc) (lowGeometry121C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (33990083507307 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry121C_hz17 hx hc) (lowGeometry121C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (291505075030037 / 25000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry121C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (33581384643460263 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry121C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (33581384643460263 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry121C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry121C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (340407 / 200000) (170367 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry121C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry121C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (3809521931227067 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry121C_hz22 hx hc) (lowGeometry121C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry121C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry121C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry121C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry121C_hz26 hx hc) (lowGeometry121C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry121C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 0 (157214128450651 / 8000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry121C_hz24 hx hc) (lowGeometry121C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (1033581384643460263 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry121C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B 1 (213658095736298511 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry121C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (479 / 1000) (512245284527775681 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry121C_hz2 hx hc) (lowGeometry121C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (479 / 1000) (33243565661506691 / 62500000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry121C_hz33 hx hc) (lowGeometry121C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (479 / 1000) (33243565661506691 / 62500000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry121C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry121C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (966418615356539737 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry121C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (466982470053825751 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry121C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (447369206311565069 / 1000000000000000000) (959 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry121C_hz2 hx hc) (lowGeometry121C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (213858720127616847 / 500000000000000000) (959 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry121C_hz38 hx hc) (lowGeometry121C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry121C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1041 / 2000) (521 / 1000) θ) : B (213858720127616847 / 500000000000000000) (959 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry121C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry121C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1041 / 2000) (521 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (401325363 / 1000000000) (142179693 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64745043 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry121C_hz12 hx hc).2
  have hrp := (lowGeometry121C_hz16 hx hc).2
  have hbn := (lowGeometry121C_hz21 hx hc).2
  have hlo := (lowGeometry121C_hz40 hx hc).1
  have hhi := (lowGeometry121C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry122W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (521 / 1000) (1043 / 2000) θ := hc

theorem lowGeometry122W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry122W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (957 / 2000) (479 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry122W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (498597 / 2000000) (499597 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry122W_hz0 hx hc) (lowGeometry122W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (499597 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry122W_hz3 hx hc) (lowGeometry122W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1396979162783039 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry122W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (4190937488349117 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry122W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (521 / 500) (1043 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry122W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry122W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry122W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1043 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry122W_hz7 hx hc) (lowGeometry122W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (7450312488349117 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry122W_hz6 hx hc) (lowGeometry122W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (7450312488349117 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry122W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry122W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (521 / 25) (1043 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry122W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1043 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry122W_hz13 hx hc) (lowGeometry122W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (7613281238349117 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry122W_hz12 hx hc) (lowGeometry122W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (7613281238349117 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry122W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry122W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1043 / 16000000) (θ * x) := bmul (lowGeometry122W_hz0 hx hc) (lowGeometry122W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (13623301985371 / 100000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry122W_hz17 hx hc) (lowGeometry122W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (466875606308507 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry122W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1400626818925521 / 20000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry122W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1400626818925521 / 20000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry122W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry122W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (521 / 125) (1043 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry122W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry122W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (2915273625665351 / 62500000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry122W_hz22 hx hc) (lowGeometry122W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry122W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry122W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry122W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry122W_hz26 hx hc) (lowGeometry122W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry122W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (49032094489222061 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry122W_hz24 hx hc) (lowGeometry122W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (21400626818925521 / 20000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry122W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (1144967070607285661 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry122W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (957 / 2000) (68554903352611229 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry122W_hz2 hx hc) (lowGeometry122W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (957 / 2000) (597471321310111893 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry122W_hz33 hx hc) (lowGeometry122W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (957 / 2000) (597471321310111893 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry122W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry122W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (18599373181074479 / 20000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry122W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (43242085341109073 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry122W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (103456689178603457 / 250000000000000000) (479 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry122W_hz2 hx hc) (lowGeometry122W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (364794662225191767 / 1000000000000000000) (479 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry122W_hz38 hx hc) (lowGeometry122W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (364794662225191767 / 1000000000000000000) (479 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry122W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry122W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (521 / 1000) (1043 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (162591637 / 500000000) (21197871 / 31250000) ∧ radiusMinus n θ lowWideWindow ≤ (23841 / 200000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry122W_hz12 hx hc).2
  have hrp := (lowGeometry122W_hz16 hx hc).2
  have hbn := (lowGeometry122W_hz21 hx hc).2
  have hlo := (lowGeometry122W_hz40 hx hc).1
  have hhi := (lowGeometry122W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry122C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (521 / 1000) (1043 / 2000) θ := hc

theorem lowGeometry122C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry122C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (957 / 2000) (479 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry122C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (498597 / 2000000) (499597 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry122C_hz0 hx hc) (lowGeometry122C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (499597 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry122C_hz3 hx hc) (lowGeometry122C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1396979162783039 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry122C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (32186399910521219 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry122C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (521 / 500) (1043 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry122C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry122C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry122C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (8147133645683309 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry122C_hz7 hx hc) (lowGeometry122C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (12954986898650891 / 200000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry122C_hz6 hx hc) (lowGeometry122C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (12954986898650891 / 200000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry122C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry122C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (406901 / 50000) (814583 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry122C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (814583 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry122C_hz13 hx hc) (lowGeometry122C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (13158632648650891 / 200000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry122C_hz12 hx hc) (lowGeometry122C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (13158632648650891 / 200000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry122C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry122C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (1043 / 16000000) (θ * x) := bmul (lowGeometry122C_hz0 hx hc) (lowGeometry122C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (13623301985371 / 100000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry122C_hz17 hx hc) (lowGeometry122C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (466875606308507 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry122C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (4201880456776563 / 125000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry122C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (4201880456776563 / 125000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry122C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry122C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (170367 / 100000) (341061 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry122C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry122C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (4766472377962849 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry122C_hz22 hx hc) (lowGeometry122C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry122C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry122C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry122C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry122C_hz26 hx hc) (lowGeometry122C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry122C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 0 (393412514333083 / 20000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry122C_hz24 hx hc) (lowGeometry122C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (129201880456776563 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry122C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B 1 (1068360058468299621 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry122C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (957 / 2000) (511744468006315519 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry122C_hz2 hx hc) (lowGeometry122C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (957 / 2000) (531415093722969669 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry122C_hz33 hx hc) (lowGeometry122C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (957 / 2000) (531415093722969669 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry122C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry122C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (120798119543223437 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry122C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (233474970962862401 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry122C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (89374218884583727 / 200000000000000000) (479 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry122C_hz2 hx hc) (lowGeometry122C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (85440093741252897 / 200000000000000000) (479 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry122C_hz38 hx hc) (lowGeometry122C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry122C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (521 / 1000) (1043 / 2000) θ) : B (85440093741252897 / 200000000000000000) (479 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry122C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry122C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (521 / 1000) (1043 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (400828681 / 1000000000) (142055403 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12954987 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry122C_hz12 hx hc).2
  have hrp := (lowGeometry122C_hz16 hx hc).2
  have hbn := (lowGeometry122C_hz21 hx hc).2
  have hlo := (lowGeometry122C_hz40 hx hc).1
  have hhi := (lowGeometry122C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry123W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (1043 / 2000) (261 / 500) θ := hc

theorem lowGeometry123W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry123W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (239 / 500) (957 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry123W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (249277 / 1000000) (249777 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry123W_hz0 hx hc) (lowGeometry123W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (249777 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry123W_hz3 hx hc) (lowGeometry123W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (1396919042929833 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry123W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (4190757128789499 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry123W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (1043 / 1000) (261 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry123W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry123W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry123W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (261 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry123W_hz7 hx hc) (lowGeometry123W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (7453257128789499 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry123W_hz6 hx hc) (lowGeometry123W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (7453257128789499 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry123W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry123W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (1043 / 50) (522 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry123W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (261 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry123W_hz13 hx hc) (lowGeometry123W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (7616382128789499 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry123W_hz12 hx hc) (lowGeometry123W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (7616382128789499 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry123W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry123W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (261 / 4000000) (θ * x) := bmul (lowGeometry123W_hz0 hx hc) (lowGeometry123W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (34126569037657 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry123W_hz17 hx hc) (lowGeometry123W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (11683590036911943 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry123W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (35050770110735829 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry123W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (35050770110735829 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry123W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry123W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (1043 / 250) (522 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry123W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry123W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (11672274842548903 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry123W_hz22 hx hc) (lowGeometry123W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry123W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry123W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry123W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry123W_hz26 hx hc) (lowGeometry123W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry123W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (49079105126316233 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry123W_hz24 hx hc) (lowGeometry123W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (535050770110735829 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry123W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (45804692255374637 / 40000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry123W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (239 / 500) (68492328888114887 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry123W_hz2 hx hc) (lowGeometry123W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (239 / 500) (597017736231235329 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry123W_hz33 hx hc) (lowGeometry123W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (239 / 500) (597017736231235329 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry123W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry123W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (464949229889264171 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry123W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (216177786374619823 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry123W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (413331927548273101 / 1000000000000000000) (957 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry123W_hz2 hx hc) (lowGeometry123W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (91063205605489217 / 250000000000000000) (957 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry123W_hz38 hx hc) (lowGeometry123W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (91063205605489217 / 250000000000000000) (957 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry123W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry123W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1043 / 2000) (261 / 500) θ) :
    OverlapGuard n θ lowWideWindow (32468591 / 100000000) (677853159 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (23850423 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry123W_hz12 hx hc).2
  have hrp := (lowGeometry123W_hz16 hx hc).2
  have hbn := (lowGeometry123W_hz21 hx hc).2
  have hlo := (lowGeometry123W_hz40 hx hc).1
  have hhi := (lowGeometry123W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry123C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (1043 / 2000) (261 / 500) θ := hc

theorem lowGeometry123C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry123C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (239 / 500) (957 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry123C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (249277 / 1000000) (249777 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry123C_hz0 hx hc) (lowGeometry123C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (249777 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry123C_hz3 hx hc) (lowGeometry123C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (1396919042929833 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry123C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (32185014749103353 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry123C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (1043 / 1000) (261 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry123C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry123C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry123C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (8154944895583293 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry123C_hz7 hx hc) (lowGeometry123C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (2592191773257461 / 40000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry123C_hz6 hx hc) (lowGeometry123C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (2592191773257461 / 40000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry123C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry123C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (814583 / 100000) (203841 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry123C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (203841 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry123C_hz13 hx hc) (lowGeometry123C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (2632959973257461 / 40000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry123C_hz12 hx hc) (lowGeometry123C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (2632959973257461 / 40000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry123C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry123C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (261 / 4000000) (θ * x) := bmul (lowGeometry123C_hz0 hx hc) (lowGeometry123C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (34126569037657 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry123C_hz17 hx hc) (lowGeometry123C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (11683590036911943 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry123C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (8412184826576599 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry123C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (8412184826576599 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry123C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry123C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (341061 / 200000) (85347 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry123C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry123C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (19084169367567457 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry123C_hz22 hx hc) (lowGeometry123C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry123C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry123C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry123C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry123C_hz26 hx hc) (lowGeometry123C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry123C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 0 (787579415079077 / 40000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry123C_hz24 hx hc) (lowGeometry123C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (258412184826576599 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry123C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B 1 (534214858134758281 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry123C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (239 / 500) (20449744769398547 / 40000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry123C_hz2 hx hc) (lowGeometry123C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (239 / 500) (2654665523059703 / 5000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry123C_hz33 hx hc) (lowGeometry123C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (239 / 500) (2654665523059703 / 5000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry123C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry123C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (241587815173423401 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry123C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (933834759044290977 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry123C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (446373014823171087 / 1000000000000000000) (957 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry123C_hz2 hx hc) (lowGeometry123C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (213341764723097081 / 500000000000000000) (957 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry123C_hz38 hx hc) (lowGeometry123C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry123C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1043 / 2000) (261 / 500) θ) : B (213341764723097081 / 500000000000000000) (957 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry123C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry123C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1043 / 2000) (261 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (400332071 / 1000000000) (283862183 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12960959 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry123C_hz12 hx hc).2
  have hrp := (lowGeometry123C_hz16 hx hc).2
  have hbn := (lowGeometry123C_hz21 hx hc).2
  have hlo := (lowGeometry123C_hz40 hx hc).1
  have hhi := (lowGeometry123C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry124W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (261 / 500) (209 / 400) θ := hc

theorem lowGeometry124W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry124W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (191 / 400) (239 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry124W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (49851 / 200000) (49951 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry124W_hz0 hx hc) (lowGeometry124W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (49951 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry124W_hz3 hx hc) (lowGeometry124W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (1117486017809619 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry124W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (3352458053428857 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry124W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (261 / 250) (209 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry124W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry124W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry124W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (209 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry124W_hz7 hx hc) (lowGeometry124W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (5964958053428857 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry124W_hz6 hx hc) (lowGeometry124W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (5964958053428857 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry124W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry124W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (522 / 25) (209 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry124W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (209 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry124W_hz13 hx hc) (lowGeometry124W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (6095583053428857 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry124W_hz12 hx hc) (lowGeometry124W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (6095583053428857 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry124W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry124W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (209 / 3200000) (θ * x) := bmul (lowGeometry124W_hz0 hx hc) (lowGeometry124W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (68390052356021 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry124W_hz17 hx hc) (lowGeometry124W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (2923825669307701 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry124W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8771477007923103 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry124W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8771477007923103 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry124W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry124W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (522 / 125) (209 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry124W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry124W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (46733820729745607 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry124W_hz22 hx hc) (lowGeometry124W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry124W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry124W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry124W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry124W_hz26 hx hc) (lowGeometry124W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry124W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (9825223152682081 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry124W_hz24 hx hc) (lowGeometry124W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (133771477007923103 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry124W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (1145267715896403161 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry124W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (191 / 400) (547437968198480711 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry124W_hz2 hx hc) (lowGeometry124W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (191 / 400) (149141020990472779 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry124W_hz33 hx hc) (lowGeometry124W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (191 / 400) (149141020990472779 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry124W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry124W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (116228522992076897 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry124W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (108072556455357983 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry124W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (82567433131893499 / 200000000000000000) (239 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry124W_hz2 hx hc) (lowGeometry124W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (36371104989605709 / 100000000000000000) (239 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry124W_hz38 hx hc) (lowGeometry124W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (36371104989605709 / 100000000000000000) (239 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry124W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry124W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (261 / 500) (209 / 400) θ) :
    OverlapGuard n θ lowWideWindow (32418867 / 100000000) (338687133 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (59649581 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry124W_hz12 hx hc).2
  have hrp := (lowGeometry124W_hz16 hx hc).2
  have hbn := (lowGeometry124W_hz21 hx hc).2
  have hlo := (lowGeometry124W_hz40 hx hc).1
  have hhi := (lowGeometry124W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry124C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (261 / 500) (209 / 400) θ := hc

theorem lowGeometry124C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry124C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (191 / 400) (239 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry124C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (49851 / 200000) (49951 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry124C_hz0 hx hc) (lowGeometry124C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (49951 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry124C_hz3 hx hc) (lowGeometry124C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (1117486017809619 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry124C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8045899328229257 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry124C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (261 / 250) (209 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry124C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry124C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry124C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8162756145483277 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry124C_hz7 hx hc) (lowGeometry124C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8104327736856267 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry124C_hz6 hx hc) (lowGeometry124C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8104327736856267 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry124C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry124C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (203841 / 25000) (163229 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry124C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (163229 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry124C_hz13 hx hc) (lowGeometry124C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8231850393106267 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry124C_hz12 hx hc) (lowGeometry124C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8231850393106267 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry124C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry124C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (209 / 3200000) (θ * x) := bmul (lowGeometry124C_hz0 hx hc) (lowGeometry124C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (68390052356021 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry124C_hz17 hx hc) (lowGeometry124C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (2923825669307701 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry124C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8420617927606179 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry124C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (8420617927606179 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry124C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry124C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (85347 / 50000) (68343 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry124C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry124C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (19102449223283517 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry124C_hz22 hx hc) (lowGeometry124C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry124C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry124C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry124C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry124C_hz26 hx hc) (lowGeometry124C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry124C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 0 (19708345037299699 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry124C_hz24 hx hc) (lowGeometry124C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (258420617927606179 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry124C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B 1 (534249726160686497 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry124C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (191 / 400) (127685684552404073 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry124C_hz2 hx hc) (lowGeometry124C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (191 / 400) (530451083246915991 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry124C_hz33 hx hc) (lowGeometry124C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (191 / 400) (530451083246915991 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry124C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry124C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (241579382072393821 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry124C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (933769565479674129 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry124C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (111468741879136099 / 250000000000000000) (239 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry124C_hz2 hx hc) (lowGeometry124C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (426166622479244697 / 1000000000000000000) (239 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry124C_hz38 hx hc) (lowGeometry124C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry124C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (261 / 500) (209 / 400) θ) : B (426166622479244697 / 1000000000000000000) (239 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry124C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry124C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (261 / 500) (209 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (99958883 / 250000000) (283613517 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32417311 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry124C_hz12 hx hc).2
  have hrp := (lowGeometry124C_hz16 hx hc).2
  have hbn := (lowGeometry124C_hz21 hx hc).2
  have hlo := (lowGeometry124C_hz40 hx hc).1
  have hhi := (lowGeometry124C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry125W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (209 / 400) (523 / 1000) θ := hc

theorem lowGeometry125W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry125W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (477 / 1000) (191 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry125W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (99693 / 400000) (99893 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry125W_hz0 hx hc) (lowGeometry125W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (99893 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry125W_hz3 hx hc) (lowGeometry125W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (2793589201189037 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry125W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (8380767603567111 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry125W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (209 / 200) (523 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry125W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry125W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry125W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (523 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry125W_hz7 hx hc) (lowGeometry125W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (14918267603567111 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry125W_hz6 hx hc) (lowGeometry125W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (14918267603567111 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry125W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry125W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (209 / 10) (523 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry125W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (523 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry125W_hz13 hx hc) (lowGeometry125W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (15245142603567111 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry125W_hz12 hx hc) (lowGeometry125W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (15245142603567111 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry125W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry125W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (523 / 8000000) (θ * x) := bmul (lowGeometry125W_hz0 hx hc) (lowGeometry125W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (137054507337527 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry125W_hz17 hx hc) (lowGeometry125W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (11707028117226293 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry125W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (35121084351678879 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry125W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (35121084351678879 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry125W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry125W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (209 / 50) (523 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry125W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry125W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (46778542089295603 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry125W_hz22 hx hc) (lowGeometry125W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry125W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry125W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry125W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry125W_hz26 hx hc) (lowGeometry125W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry125W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (24586563200252289 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry125W_hz24 hx hc) (lowGeometry125W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (535121084351678879 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry125W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (1145418299670866489 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry125W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (477 / 1000) (546937238092838749 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry125W_hz2 hx hc) (lowGeometry125W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (477 / 1000) (596110364493343327 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry125W_hz33 hx hc) (lowGeometry125W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (477 / 1000) (596110364493343327 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry125W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry125W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (464878915648321121 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry125W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (13507025388397429 / 15625000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry125W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (51542808882124589 / 125000000000000000) (191 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry125W_hz2 hx hc) (lowGeometry125W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (181584672328246067 / 500000000000000000) (191 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry125W_hz38 hx hc) (lowGeometry125W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (181584672328246067 / 500000000000000000) (191 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry125W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry125W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (209 / 400) (523 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (323691553 / 1000000000) (338447597 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (119346141 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry125W_hz12 hx hc).2
  have hrp := (lowGeometry125W_hz16 hx hc).2
  have hbn := (lowGeometry125W_hz21 hx hc).2
  have hlo := (lowGeometry125W_hz40 hx hc).1
  have hhi := (lowGeometry125W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry125C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (209 / 400) (523 / 1000) θ := hc

theorem lowGeometry125C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry125C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (477 / 1000) (191 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry125C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (99693 / 400000) (99893 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry125C_hz0 hx hc) (lowGeometry125C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (99893 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry125C_hz3 hx hc) (lowGeometry125C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (2793589201189037 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry125C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (32182147597697707 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry125C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (209 / 200) (523 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry125C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry125C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry125C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (8170567395383261 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry125C_hz7 hx hc) (lowGeometry125C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (64864417179230751 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry125C_hz6 hx hc) (lowGeometry125C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (64864417179230751 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry125C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry125C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (163229 / 20000) (408463 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry125C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (408463 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry125C_hz13 hx hc) (lowGeometry125C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (65885574679230751 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry125C_hz12 hx hc) (lowGeometry125C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (65885574679230751 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry125C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry125C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (523 / 8000000) (θ * x) := bmul (lowGeometry125C_hz0 hx hc) (lowGeometry125C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (137054507337527 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry125C_hz17 hx hc) (lowGeometry125C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (11707028117226293 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry125C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (8429060244402931 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry125C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (8429060244402931 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry125C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry125C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (68343 / 40000) (171021 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry125C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry125C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (9560364539499789 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry125C_hz22 hx hc) (lowGeometry125C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry125C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry125C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry125C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry125C_hz26 hx hc) (lowGeometry125C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry125C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 0 (9863602348811237 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry125C_hz24 hx hc) (lowGeometry125C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (258429060244402931 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry125C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B 1 (133571158357610479 / 125000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry125C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (477 / 1000) (51024182492607203 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry125C_hz2 hx hc) (lowGeometry125C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (477 / 1000) (66246128702961813 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry125C_hz33 hx hc) (lowGeometry125C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (477 / 1000) (66246128702961813 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry125C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry125C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (241570939755597069 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry125C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (186740860590087387 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry125C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (445376952507358417 / 1000000000000000000) (191 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry125C_hz2 hx hc) (lowGeometry125C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (425649747809735943 / 1000000000000000000) (191 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry125C_hz38 hx hc) (lowGeometry125C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry125C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (209 / 400) (523 / 1000) θ) : B (425649747809735943 / 1000000000000000000) (191 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry125C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry125C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (209 / 400) (523 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (49917383 / 125000000) (35420601 / 62500000) ∧ radiusMinus n θ lowCoreWindow ≤ (32432209 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry125C_hz12 hx hc).2
  have hrp := (lowGeometry125C_hz16 hx hc).2
  have hbn := (lowGeometry125C_hz21 hx hc).2
  have hlo := (lowGeometry125C_hz40 hx hc).1
  have hhi := (lowGeometry125C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry126W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (523 / 1000) (1047 / 2000) θ := hc

theorem lowGeometry126W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry126W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (953 / 2000) (477 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry126W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (498419 / 2000000) (499419 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry126W_hz0 hx hc) (lowGeometry126W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (499419 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry126W_hz3 hx hc) (lowGeometry126W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (5586921110951899 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry126W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (16760763332855697 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry126W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (523 / 500) (1047 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry126W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry126W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry126W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1047 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry126W_hz7 hx hc) (lowGeometry126W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (29848263332855697 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry126W_hz6 hx hc) (lowGeometry126W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (29848263332855697 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry126W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry126W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (523 / 25) (1047 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry126W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1047 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry126W_hz13 hx hc) (lowGeometry126W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (30502638332855697 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry126W_hz12 hx hc) (lowGeometry126W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (30502638332855697 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry126W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry126W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1047 / 16000000) (θ * x) := bmul (lowGeometry126W_hz0 hx hc) (lowGeometry126W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (4291546432319 / 31250000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry126W_hz17 hx hc) (lowGeometry126W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (5859383197790703 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry126W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (17578149593372109 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry126W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (17578149593372109 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry126W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry126W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (523 / 125) (1047 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry126W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry126W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (46823263448845599 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry126W_hz22 hx hc) (lowGeometry126W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry126W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry126W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry126W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry126W_hz26 hx hc) (lowGeometry126W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry126W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (49220137037598751 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry126W_hz24 hx hc) (lowGeometry126W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (267578149593372109 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry126W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (1145569058237008361 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry126W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (953 / 2000) (546436440779052989 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry126W_hz2 hx hc) (lowGeometry126W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (953 / 2000) (29782828890832587 / 50000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry126W_hz33 hx hc) (lowGeometry126W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (953 / 2000) (29782828890832587 / 50000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry126W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry126W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (232421850406627891 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry126W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (108039833092881827 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry126W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (102961960937516381 / 250000000000000000) (477 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry126W_hz2 hx hc) (lowGeometry126W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (362627706712466773 / 1000000000000000000) (477 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry126W_hz38 hx hc) (lowGeometry126W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (362627706712466773 / 1000000000000000000) (477 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry126W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry126W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (523 / 1000) (1047 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (323194559 / 1000000000) (676415943 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (59696527 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry126W_hz12 hx hc).2
  have hrp := (lowGeometry126W_hz16 hx hc).2
  have hbn := (lowGeometry126W_hz21 hx hc).2
  have hlo := (lowGeometry126W_hz40 hx hc).1
  have hhi := (lowGeometry126W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry126C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (523 / 1000) (1047 / 2000) θ := hc

theorem lowGeometry126C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry126C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (953 / 2000) (477 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry126C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (498419 / 2000000) (499419 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry126C_hz0 hx hc) (lowGeometry126C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (499419 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry126C_hz3 hx hc) (lowGeometry126C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (5586921110951899 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry126C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (32180665599082939 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry126C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (523 / 500) (1047 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry126C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry126C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry126C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1635675729056649 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry126C_hz7 hx hc) (lowGeometry126C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (64894180180215919 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry126C_hz6 hx hc) (lowGeometry126C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (64894180180215919 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry126C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry126C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (408463 / 50000) (817707 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry126C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (817707 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry126C_hz13 hx hc) (lowGeometry126C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (65916313930215919 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry126C_hz12 hx hc) (lowGeometry126C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (65916313930215919 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry126C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry126C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (1047 / 16000000) (θ * x) := bmul (lowGeometry126C_hz0 hx hc) (lowGeometry126C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (4291546432319 / 31250000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry126C_hz17 hx hc) (lowGeometry126C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (5859383197790703 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry126C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (675000944385489 / 20000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry126C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (675000944385489 / 20000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry126C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry126C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (171021 / 100000) (342369 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry126C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry126C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (19139008934715639 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry126C_hz22 hx hc) (lowGeometry126C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry126C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry126C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry126C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry126C_hz26 hx hc) (lowGeometry126C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry126C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 0 (78984257431781 / 4000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry126C_hz24 hx hc) (lowGeometry126C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (20675000944385489 / 20000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry126C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B 1 (267159790031463039 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry126C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (953 / 2000) (509740879380031479 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry126C_hz2 hx hc) (lowGeometry126C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (953 / 2000) (529486943737976729 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry126C_hz33 hx hc) (lowGeometry126C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (953 / 2000) (529486943737976729 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry126C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry126C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (19324999055614511 / 20000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry126C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (186727794249750871 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry126C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (8897579396000629 / 20000000000000000) (477 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry126C_hz2 hx hc) (lowGeometry126C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (2125664527210431 / 5000000000000000) (477 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry126C_hz38 hx hc) (lowGeometry126C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry126C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (523 / 1000) (1047 / 2000) θ) : B (2125664527210431 / 5000000000000000) (477 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry126C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry126C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (523 / 1000) (1047 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (199421333 / 500000000) (566232113 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64894181 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry126C_hz12 hx hc).2
  have hrp := (lowGeometry126C_hz16 hx hc).2
  have hbn := (lowGeometry126C_hz21 hx hc).2
  have hlo := (lowGeometry126C_hz40 hx hc).1
  have hhi := (lowGeometry126C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry127W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (1047 / 2000) (131 / 250) θ := hc

theorem lowGeometry127W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry127W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (119 / 250) (953 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry127W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (124593 / 500000) (124843 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry127W_hz0 hx hc) (lowGeometry127W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (124843 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry127W_hz3 hx hc) (lowGeometry127W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (5586658213995197 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry127W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (16759974641985591 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry127W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (1047 / 1000) (131 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry127W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry127W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry127W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (131 / 2500) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry127W_hz7 hx hc) (lowGeometry127W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (29859974641985591 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry127W_hz6 hx hc) (lowGeometry127W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (29859974641985591 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry127W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry127W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (1047 / 50) (524 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry127W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (131 / 50000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry127W_hz13 hx hc) (lowGeometry127W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (30514974641985591 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry127W_hz12 hx hc) (lowGeometry127W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (30514974641985591 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry127W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry127W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (131 / 2000000) (θ * x) := bmul (lowGeometry127W_hz0 hx hc) (lowGeometry127W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (137605042016807 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry127W_hz17 hx hc) (lowGeometry127W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (11730517551106047 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry127W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (35191552653318141 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry127W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (35191552653318141 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry127W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry127W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (1047 / 250) (524 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry127W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry127W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (9373596961679119 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry127W_hz22 hx hc) (lowGeometry127W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry127W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry127W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry127W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry127W_hz26 hx hc) (lowGeometry127W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry127W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (12316786918673231 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry127W_hz24 hx hc) (lowGeometry127W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (535191552653318141 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry127W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (1145719992125877617 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry127W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (119 / 250) (109187115249596137 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry127W_hz2 hx hc) (lowGeometry127W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (119 / 250) (595202723922673609 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry127W_hz33 hx hc) (lowGeometry127W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (119 / 250) (595202723922673609 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry127W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry127W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (464808447346681859 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry127W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (108023446362416561 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry127W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (51419160468510283 / 125000000000000000) (953 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry127W_hz2 hx hc) (lowGeometry127W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (18104306803669467 / 50000000000000000) (953 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry127W_hz38 hx hc) (lowGeometry127W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (18104306803669467 / 50000000000000000) (953 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry127W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry127W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1047 / 2000) (131 / 250) θ) :
    OverlapGuard n θ lowWideWindow (40337211 / 125000000) (675936513 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (119439899 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry127W_hz12 hx hc).2
  have hrp := (lowGeometry127W_hz16 hx hc).2
  have hbn := (lowGeometry127W_hz21 hx hc).2
  have hlo := (lowGeometry127W_hz40 hx hc).1
  have hhi := (lowGeometry127W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry127C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (1047 / 2000) (131 / 250) θ := hc

theorem lowGeometry127C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry127C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (119 / 250) (953 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry127C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (124593 / 500000) (124843 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry127C_hz0 hx hc) (lowGeometry127C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (124843 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry127C_hz3 hx hc) (lowGeometry127C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (5586658213995197 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry127C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (6435830262522467 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry127C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (1047 / 1000) (131 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry127C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry127C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry127C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (8186189895183229 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry127C_hz7 hx hc) (lowGeometry127C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (64923910893345251 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry127C_hz6 hx hc) (lowGeometry127C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (64923910893345251 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry127C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry127C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (817707 / 100000) (102311 / 12500) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry127C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (102311 / 100000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry127C_hz13 hx hc) (lowGeometry127C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (65947020893345251 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry127C_hz12 hx hc) (lowGeometry127C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (65947020893345251 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry127C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry127C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (131 / 2000000) (θ * x) := bmul (lowGeometry127C_hz0 hx hc) (lowGeometry127C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (137605042016807 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry127C_hz17 hx hc) (lowGeometry127C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (11730517551106047 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry127C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (4222986318398177 / 125000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry127C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (4222986318398177 / 125000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry127C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry127C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (342369 / 200000) (42837 / 25000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry127C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry127C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (191572887904317 / 10000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry127C_hz22 hx hc) (lowGeometry127C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry127C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry127C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry127C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry127C_hz26 hx hc) (lowGeometry127C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry127C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 0 (790596960730721 / 40000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry127C_hz24 hx hc) (lowGeometry127C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (129222986318398177 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry127C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B 1 (1068709132354875037 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry127C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (119 / 250) (127309975391774489 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry127C_hz2 hx hc) (lowGeometry127C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (119 / 250) (529004825585365981 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry127C_hz33 hx hc) (lowGeometry127C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (119 / 250) (529004825585365981 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry127C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry127C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (120777013681601823 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry127C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (233393392541533343 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry127C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (88876203879815897 / 200000000000000000) (953 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry127C_hz2 hx hc) (lowGeometry127C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (21230804769040573 / 50000000000000000) (953 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry127C_hz38 hx hc) (lowGeometry127C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry127C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1047 / 2000) (131 / 250) θ) : B (21230804769040573 / 50000000000000000) (953 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry127C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry127C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1047 / 2000) (131 / 250) θ) :
    OverlapGuard n θ lowCoreWindow (19917317 / 50000000) (141433631 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (64923911 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry127C_hz12 hx hc).2
  have hrp := (lowGeometry127C_hz16 hx hc).2
  have hbn := (lowGeometry127C_hz21 hx hc).2
  have hlo := (lowGeometry127C_hz40 hx hc).1
  have hhi := (lowGeometry127C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

end BstLean.BlueprintLow
