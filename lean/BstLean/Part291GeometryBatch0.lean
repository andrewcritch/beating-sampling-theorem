import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part199 BstLean.Part255 BstLean.Part264b
theorem lowGeometry0W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (23 / 50) (921 / 2000) θ := hc

theorem lowGeometry0W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry0W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (1079 / 2000) (27 / 50) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (24817 / 100000) (24867 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry0W_hz0 hx hc) (lowGeometry0W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (24867 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry0W_hz3 hx hc) (lowGeometry0W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (5575280262013741 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry0W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (16725840786041223 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry0W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (23 / 25) (921 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry0W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry0W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry0W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (921 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry0W_hz7 hx hc) (lowGeometry0W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (28238340786041223 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry0W_hz6 hx hc) (lowGeometry0W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (28238340786041223 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry0W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry0W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (92 / 5) (921 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry0W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (921 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry0W_hz13 hx hc) (lowGeometry0W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (28813965786041223 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry0W_hz12 hx hc) (lowGeometry0W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (28813965786041223 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry0W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry0W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (921 / 16000000) (θ * x) := bmul (lowGeometry0W_hz0 hx hc) (lowGeometry0W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (21339202965709 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry0W_hz17 hx hc) (lowGeometry0W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (2582344075986789 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry0W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (7747032227960367 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry0W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (7747032227960367 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry0W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry0W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (92 / 25) (921 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry0W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry0W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (41188372145546129 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry0W_hz22 hx hc) (lowGeometry0W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry0W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry0W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry0W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry0W_hz26 hx hc) (lowGeometry0W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry0W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (43296796763732999 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry0W_hz24 hx hc) (lowGeometry0W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (132747032227960367 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry0W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (1127793572181193493 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry0W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (1079 / 2000) (609008528977844487 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry0W_hz2 hx hc) (lowGeometry0W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (1079 / 2000) (326152662870788743 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry0W_hz33 hx hc) (lowGeometry0W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (1079 / 2000) (326152662870788743 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry0W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry0W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (117252967772039633 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry0W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (219972135221615437 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry0W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (474699867808246113 / 1000000000000000000) (27 / 50) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry0W_hz2 hx hc) (lowGeometry0W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (215701535522256557 / 500000000000000000) (27 / 50) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry0W_hz38 hx hc) (lowGeometry0W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (215701535522256557 / 500000000000000000) (27 / 50) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry0W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry0W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (23 / 50) (921 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (193409909 / 500000000) (367683783 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (28238341 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry0W_hz12 hx hc).2
  have hrp := (lowGeometry0W_hz16 hx hc).2
  have hbn := (lowGeometry0W_hz21 hx hc).2
  have hlo := (lowGeometry0W_hz40 hx hc).1
  have hhi := (lowGeometry0W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry0C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (23 / 50) (921 / 2000) θ := hc

theorem lowGeometry0C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry0C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (1079 / 2000) (27 / 50) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (24817 / 100000) (24867 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry0C_hz0 hx hc) (lowGeometry0C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (24867 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry0C_hz3 hx hc) (lowGeometry0C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (5575280262013741 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry0C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (32113614309199149 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry0C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (23 / 25) (921 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry0C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry0C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry0C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (5755328926308209 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry0C_hz7 hx hc) (lowGeometry0C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (30445129470370097 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry0C_hz6 hx hc) (lowGeometry0C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (30445129470370097 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry0C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry0C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (17963 / 2500) (719301 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry0C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (719301 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry0C_hz13 hx hc) (lowGeometry0C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (30894692595370097 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry0C_hz12 hx hc) (lowGeometry0C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (30894692595370097 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry0C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry0C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (921 / 16000000) (θ * x) := bmul (lowGeometry0C_hz0 hx hc) (lowGeometry0C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (21339202965709 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry0C_hz17 hx hc) (lowGeometry0C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (2582344075986789 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry0C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (2974860375536781 / 100000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry0C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (2974860375536781 / 100000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry0C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry0C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (7521 / 5000) (301167 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry0C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry0C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (841787355724599 / 50000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry0C_hz22 hx hc) (lowGeometry0C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry0C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry0C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry0C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry0C_hz26 hx hc) (lowGeometry0C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry0C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 0 (868487357863781 / 50000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry0C_hz24 hx hc) (lowGeometry0C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (102974860375536781 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry0C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B 1 (33136943341754047 / 31250000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry0C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (1079 / 2000) (572606380945509933 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry0C_hz2 hx hc) (lowGeometry0C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (1079 / 2000) (589976128102785553 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry0C_hz33 hx hc) (lowGeometry0C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (1079 / 2000) (589976128102785553 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry0C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry0C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (97025139624463219 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry0C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (941387771914658263 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry0C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (126969675736989533 / 250000000000000000) (27 / 50) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry0C_hz2 hx hc) (lowGeometry0C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (30656809736917657 / 62500000000000000) (27 / 50) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry0C_hz38 hx hc) (lowGeometry0C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry0C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (921 / 2000) θ) : B (30656809736917657 / 62500000000000000) (27 / 50) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry0C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry0C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (23 / 50) (921 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (57745557 / 125000000) (125645833 / 200000000) ∧ radiusMinus n θ lowCoreWindow ≤ (60890259 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry0C_hz12 hx hc).2
  have hrp := (lowGeometry0C_hz16 hx hc).2
  have hbn := (lowGeometry0C_hz21 hx hc).2
  have hlo := (lowGeometry0C_hz40 hx hc).1
  have hhi := (lowGeometry0C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry1W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (921 / 2000) (461 / 1000) θ := hc

theorem lowGeometry1W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry1W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (539 / 1000) (1079 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (496419 / 2000000) (497419 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry1W_hz0 hx hc) (lowGeometry1W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (497419 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry1W_hz3 hx hc) (lowGeometry1W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (5575723047282747 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry1W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (16727169141848241 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry1W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (921 / 1000) (461 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry1W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry1W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry1W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (461 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry1W_hz7 hx hc) (lowGeometry1W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (28252169141848241 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry1W_hz6 hx hc) (lowGeometry1W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (28252169141848241 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry1W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry1W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (921 / 50) (461 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry1W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (461 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry1W_hz13 hx hc) (lowGeometry1W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (28828419141848241 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry1W_hz12 hx hc) (lowGeometry1W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (28828419141848241 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry1W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry1W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (461 / 8000000) (θ * x) := bmul (lowGeometry1W_hz0 hx hc) (lowGeometry1W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (106910946196661 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry1W_hz17 hx hc) (lowGeometry1W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (2067954991740981 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry1W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (6203864975222943 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry1W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (6203864975222943 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry1W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry1W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (921 / 250) (461 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry1W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry1W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (10308273376274031 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry1W_hz22 hx hc) (lowGeometry1W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry1W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry1W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry1W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry1W_hz26 hx hc) (lowGeometry1W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry1W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (43343807400827171 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry1W_hz24 hx hc) (lowGeometry1W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (106203864975222943 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry1W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (1127926093567538657 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry1W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (539 / 1000) (304258063739843553 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry1W_hz2 hx hc) (lowGeometry1W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (539 / 1000) (651859934880514277 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry1W_hz33 hx hc) (lowGeometry1W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (539 / 1000) (651859934880514277 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry1W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry1W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (93796135024777057 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry1W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (109971436819827617 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry1W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (118549208891774171 / 250000000000000000) (1079 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry1W_hz2 hx hc) (lowGeometry1W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (430853028166269513 / 1000000000000000000) (1079 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry1W_hz38 hx hc) (lowGeometry1W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (430853028166269513 / 1000000000000000000) (1079 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry1W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry1W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (921 / 2000) (461 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (193153297 / 500000000) (734911287 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (113008677 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry1W_hz12 hx hc).2
  have hrp := (lowGeometry1W_hz16 hx hc).2
  have hbn := (lowGeometry1W_hz21 hx hc).2
  have hlo := (lowGeometry1W_hz40 hx hc).1
  have hhi := (lowGeometry1W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry1C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (921 / 2000) (461 / 1000) θ := hc

theorem lowGeometry1C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry1C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (539 / 1000) (1079 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (496419 / 2000000) (497419 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry1C_hz0 hx hc) (lowGeometry1C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (497419 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry1C_hz3 hx hc) (lowGeometry1C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (5575723047282747 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry1C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (32116164752348623 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry1C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (921 / 1000) (461 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry1C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry1C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry1C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (28807889631140981 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry1C_hz7 hx hc) (lowGeometry1C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (15231013595872401 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry1C_hz6 hx hc) (lowGeometry1C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (15231013595872401 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry1C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry1C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (719301 / 100000) (360041 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry1C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (360041 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry1C_hz13 hx hc) (lowGeometry1C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (15456039220872401 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry1C_hz12 hx hc) (lowGeometry1C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (15456039220872401 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry1C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry1C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (461 / 8000000) (θ * x) := bmul (lowGeometry1C_hz0 hx hc) (lowGeometry1C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (106910946196661 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry1C_hz17 hx hc) (lowGeometry1C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (2067954991740981 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry1C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (29778551881070127 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry1C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (29778551881070127 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry1C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry1C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (301167 / 200000) (150747 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry1C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry1C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (16854026970208041 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry1C_hz22 hx hc) (lowGeometry1C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry1C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry1C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry1C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry1C_hz26 hx hc) (lowGeometry1C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry1C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 0 (3477721363519679 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry1C_hz24 hx hc) (lowGeometry1C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (1029778551881070127 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry1C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B 1 (13255548323928423 / 12500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry1C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (539 / 1000) (572109465660750737 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry1C_hz2 hx hc) (lowGeometry1C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (539 / 1000) (147374518119587283 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry1C_hz33 hx hc) (lowGeometry1C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (539 / 1000) (147374518119587283 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry1C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry1C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (970221448118929873 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry1C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (941329658389993331 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry1C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (101475337174441281 / 200000000000000000) (1079 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry1C_hz2 hx hc) (lowGeometry1C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (48998807905460801 / 100000000000000000) (1079 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry1C_hz38 hx hc) (lowGeometry1C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry1C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (921 / 2000) (461 / 1000) θ) : B (48998807905460801 / 100000000000000000) (1079 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry1C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry1C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (921 / 2000) (461 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (461458779 / 1000000000) (39233919 / 62500000) ∧ radiusMinus n θ lowCoreWindow ≤ (12184811 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry1C_hz12 hx hc).2
  have hrp := (lowGeometry1C_hz16 hx hc).2
  have hbn := (lowGeometry1C_hz21 hx hc).2
  have hlo := (lowGeometry1C_hz40 hx hc).1
  have hhi := (lowGeometry1C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry2W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (461 / 1000) (923 / 2000) θ := hc

theorem lowGeometry2W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry2W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (1077 / 2000) (539 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (496497 / 2000000) (497497 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry2W_hz0 hx hc) (lowGeometry2W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (497497 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry2W_hz3 hx hc) (lowGeometry2W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (5576160193179533 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry2W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (16728480579538599 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry2W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (461 / 500) (923 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry2W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry2W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry2W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (923 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry2W_hz7 hx hc) (lowGeometry2W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (28265980579538599 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry2W_hz6 hx hc) (lowGeometry2W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (28265980579538599 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry2W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry2W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (461 / 25) (923 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry2W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (923 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry2W_hz13 hx hc) (lowGeometry2W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (28842855579538599 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry2W_hz12 hx hc) (lowGeometry2W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (28842855579538599 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry2W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry2W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (923 / 16000000) (θ * x) := bmul (lowGeometry2W_hz0 hx hc) (lowGeometry2W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (53563138347261 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry2W_hz17 hx hc) (lowGeometry2W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (2070036489480531 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry2W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (6210109468441593 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry2W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (6210109468441593 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry2W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry2W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (461 / 125) (923 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry2W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry2W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (1031945371616153 / 25000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry2W_hz22 hx hc) (lowGeometry2W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry2W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry2W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry2W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry2W_hz26 hx hc) (lowGeometry2W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry2W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (677981531842521 / 15625000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry2W_hz24 hx hc) (lowGeometry2W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (106210109468441593 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry2W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (1128058735329834653 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry2W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (1077 / 2000) (304011829171390439 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry2W_hz2 hx hc) (lowGeometry2W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (1077 / 2000) (325707238190351111 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry2W_hz33 hx hc) (lowGeometry2W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (1077 / 2000) (325707238190351111 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry2W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry2W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (93789890531558407 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry2W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (219913589148042733 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry2W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (236846935512442023 / 500000000000000000) (539 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry2W_hz2 hx hc) (lowGeometry2W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (215151526493481351 / 500000000000000000) (539 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry2W_hz38 hx hc) (lowGeometry2W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (215151526493481351 / 500000000000000000) (539 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry2W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry2W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (461 / 1000) (923 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (385793507 / 1000000000) (734454819 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (113063923 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry2W_hz12 hx hc).2
  have hrp := (lowGeometry2W_hz16 hx hc).2
  have hbn := (lowGeometry2W_hz21 hx hc).2
  have hlo := (lowGeometry2W_hz40 hx hc).1
  have hhi := (lowGeometry2W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry2C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (461 / 1000) (923 / 2000) θ := hc

theorem lowGeometry2C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry2C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (1077 / 2000) (539 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (496497 / 2000000) (497497 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry2C_hz0 hx hc) (lowGeometry2C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (497497 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry2C_hz3 hx hc) (lowGeometry2C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (5576160193179533 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry2C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (32118682712714111 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry2C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (461 / 500) (923 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry2C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry2C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry2C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (28839134630740917 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry2C_hz7 hx hc) (lowGeometry2C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (15239454335863757 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry2C_hz6 hx hc) (lowGeometry2C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (15239454335863757 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry2C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry2C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (360041 / 50000) (720863 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry2C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (720863 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry2C_hz13 hx hc) (lowGeometry2C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (15464724023363757 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry2C_hz12 hx hc) (lowGeometry2C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (15464724023363757 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry2C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry2C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (923 / 16000000) (θ * x) := bmul (lowGeometry2C_hz0 hx hc) (lowGeometry2C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (53563138347261 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry2C_hz17 hx hc) (lowGeometry2C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (2070036489480531 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry2C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (29808525448519647 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry2C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (29808525448519647 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry2C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry2C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (150747 / 100000) (301821 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry2C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry2C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (8436153412962051 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry2C_hz22 hx hc) (lowGeometry2C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry2C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry2C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry2C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry2C_hz26 hx hc) (lowGeometry2C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry2C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 0 (1740746647792117 / 100000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry2C_hz24 hx hc) (lowGeometry2C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (1029808525448519647 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry2C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B 1 (530252799543227169 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry2C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (1077 / 2000) (571612517907598889 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry2C_hz2 hx hc) (lowGeometry2C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (1077 / 2000) (589019984385520059 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry2C_hz33 hx hc) (lowGeometry2C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (1077 / 2000) (589019984385520059 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry2C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry2C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (970191474551480353 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry2C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (941271497292375749 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry2C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (25343735064597217 / 50000000000000000) (539 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry2C_hz2 hx hc) (lowGeometry2C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (48946723481402317 / 100000000000000000) (539 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry2C_hz38 hx hc) (lowGeometry2C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry2C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (461 / 1000) (923 / 2000) θ) : B (48946723481402317 / 100000000000000000) (539 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry2C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry2C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (461 / 1000) (923 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (460953179 / 1000000000) (627256151 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (30478909 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry2C_hz12 hx hc).2
  have hrp := (lowGeometry2C_hz16 hx hc).2
  have hbn := (lowGeometry2C_hz21 hx hc).2
  have hlo := (lowGeometry2C_hz40 hx hc).1
  have hhi := (lowGeometry2C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry3W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (923 / 2000) (231 / 500) θ := hc

theorem lowGeometry3W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry3W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (269 / 500) (1077 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry3W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (248287 / 1000000) (248787 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry3W_hz0 hx hc) (lowGeometry3W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (248787 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry3W_hz3 hx hc) (lowGeometry3W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (5576591701030299 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry3W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (16729775103090897 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry3W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (923 / 1000) (231 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry3W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry3W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry3W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (231 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry3W_hz7 hx hc) (lowGeometry3W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (28279775103090897 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry3W_hz6 hx hc) (lowGeometry3W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (28279775103090897 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry3W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry3W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (923 / 50) (462 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry3W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (231 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry3W_hz13 hx hc) (lowGeometry3W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (28857275103090897 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry3W_hz12 hx hc) (lowGeometry3W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (28857275103090897 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry3W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry3W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (231 / 4000000) (θ * x) := bmul (lowGeometry3W_hz0 hx hc) (lowGeometry3W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (21468401486989 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry3W_hz17 hx hc) (lowGeometry3W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (414423951884917 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry3W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (1243271855654751 / 20000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry3W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (1243271855654751 / 20000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry3W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry3W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (923 / 250) (462 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry3W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry3W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (10330634056049029 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry3W_hz22 hx hc) (lowGeometry3W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry3W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry3W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry3W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry3W_hz26 hx hc) (lowGeometry3W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry3W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (43437828675015517 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry3W_hz24 hx hc) (lowGeometry3W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (21243271855654751 / 20000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry3W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (1128191497833133121 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry3W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (269 / 500) (303765560791571093 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry3W_hz2 hx hc) (lowGeometry3W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (269 / 500) (650968950258157703 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry3W_hz33 hx hc) (lowGeometry3W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (269 / 500) (650968950258157703 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry3W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry3W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (18756728144345249 / 20000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry3W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (21988428167554573 / 25000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry3W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (47319097416577441 / 100000000000000000) (1077 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry3W_hz2 hx hc) (lowGeometry3W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (429753145490758893 / 1000000000000000000) (1077 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry3W_hz38 hx hc) (lowGeometry3W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (429753145490758893 / 1000000000000000000) (1077 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry3W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry3W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (923 / 2000) (231 / 500) θ) :
    OverlapGuard n θ lowWideWindow (385280557 / 1000000000) (733998163 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (113119101 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry3W_hz12 hx hc).2
  have hrp := (lowGeometry3W_hz16 hx hc).2
  have hbn := (lowGeometry3W_hz21 hx hc).2
  have hlo := (lowGeometry3W_hz40 hx hc).1
  have hhi := (lowGeometry3W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry3C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (923 / 2000) (231 / 500) θ := hc

theorem lowGeometry3C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry3C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (269 / 500) (1077 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry3C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (248287 / 1000000) (248787 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry3C_hz0 hx hc) (lowGeometry3C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (248787 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry3C_hz3 hx hc) (lowGeometry3C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (5576591701030299 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry3C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (32121168197934523 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry3C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (923 / 1000) (231 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry3C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry3C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry3C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (28870379630340853 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry3C_hz7 hx hc) (lowGeometry3C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (3811971739267211 / 62500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry3C_hz6 hx hc) (lowGeometry3C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (3811971739267211 / 62500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry3C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry3C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (720863 / 100000) (180411 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry3C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (180411 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry3C_hz13 hx hc) (lowGeometry3C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (3868350176767211 / 62500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry3C_hz12 hx hc) (lowGeometry3C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (3868350176767211 / 62500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry3C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry3C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (231 / 4000000) (θ * x) := bmul (lowGeometry3C_hz0 hx hc) (lowGeometry3C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (21468401486989 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry3C_hz17 hx hc) (lowGeometry3C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (414423951884917 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry3C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (3729815566964253 / 125000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry3C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (3729815566964253 / 125000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry3C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry3C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (301821 / 200000) (75537 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry3C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry3C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (16890586681640163 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry3C_hz22 hx hc) (lowGeometry3C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry3C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry3C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry3C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry3C_hz26 hx hc) (lowGeometry3C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry3C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 0 (3485265227648789 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry3C_hz24 hx hc) (lowGeometry3C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (128729815566964253 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry3C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B 1 (132570923327237057 / 125000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry3C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (269 / 500) (285557768846868621 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry3C_hz2 hx hc) (lowGeometry3C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (269 / 500) (588541863831981187 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry3C_hz33 hx hc) (lowGeometry3C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (269 / 500) (588541863831981187 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry3C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry3C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (121270184433035747 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry3C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (941213288475040359 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry3C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (506372749199571713 / 1000000000000000000) (1077 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry3C_hz2 hx hc) (lowGeometry3C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (61118302882665971 / 125000000000000000) (1077 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry3C_hz38 hx hc) (lowGeometry3C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry3C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (923 / 2000) (231 / 500) θ) : B (61118302882665971 / 125000000000000000) (1077 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry3C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry3C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (923 / 2000) (231 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (230223829 / 500000000) (626769507 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15247887 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry3C_hz12 hx hc).2
  have hrp := (lowGeometry3C_hz16 hx hc).2
  have hbn := (lowGeometry3C_hz21 hx hc).2
  have hlo := (lowGeometry3C_hz40 hx hc).1
  have hhi := (lowGeometry3C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry4W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (231 / 500) (37 / 80) θ := hc

theorem lowGeometry4W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry4W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (43 / 80) (269 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (9933 / 40000) (9953 / 40000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry4W_hz0 hx hc) (lowGeometry4W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (9953 / 320000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry4W_hz3 hx hc) (lowGeometry4W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (1115403514428747 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry4W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (3346210543286241 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry4W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (231 / 250) (37 / 40) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry4W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry4W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry4W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (37 / 800) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry4W_hz7 hx hc) (lowGeometry4W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (5658710543286241 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry4W_hz6 hx hc) (lowGeometry4W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (5658710543286241 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry4W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry4W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (462 / 25) (37 / 2) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry4W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (37 / 16000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry4W_hz13 hx hc) (lowGeometry4W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (5774335543286241 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry4W_hz12 hx hc) (lowGeometry4W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (5774335543286241 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry4W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry4W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (37 / 640000) (θ * x) := bmul (lowGeometry4W_hz0 hx hc) (lowGeometry4W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (26889534883721 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry4W_hz17 hx hc) (lowGeometry4W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (2074204807003243 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry4W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (6222614421009729 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry4W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (6222614421009729 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry4W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry4W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (462 / 125) (37 / 10) (θ * (8 : ℝ)) := bmul (lowGeometry4W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry4W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (646363399746033 / 15625000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry4W_hz22 hx hc) (lowGeometry4W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry4W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry4W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry4W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry4W_hz26 hx hc) (lowGeometry4W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry4W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (43484839312109689 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry4W_hz24 hx hc) (lowGeometry4W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (106222614421009729 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry4W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (225664876288690081 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry4W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (43 / 80) (303519258608288159 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry4W_hz2 hx hc) (lowGeometry4W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (43 / 80) (650523356528686007 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry4W_hz33 hx hc) (lowGeometry4W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (43 / 80) (650523356528686007 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry4W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry4W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (93777385578990271 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry4W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (219854951150765311 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry4W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (236344072487072709 / 500000000000000000) (269 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry4W_hz2 hx hc) (lowGeometry4W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (429203305662035729 / 1000000000000000000) (269 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry4W_hz38 hx hc) (lowGeometry4W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (429203305662035729 / 1000000000000000000) (269 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry4W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry4W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (231 / 500) (37 / 80) θ) :
    OverlapGuard n θ lowWideWindow (1502999 / 3906250) (733541317 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (113174211 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry4W_hz12 hx hc).2
  have hrp := (lowGeometry4W_hz16 hx hc).2
  have hbn := (lowGeometry4W_hz21 hx hc).2
  have hlo := (lowGeometry4W_hz40 hx hc).1
  have hhi := (lowGeometry4W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry4C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (231 / 500) (37 / 80) θ := hc

theorem lowGeometry4C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry4C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (43 / 80) (269 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (9933 / 40000) (9953 / 40000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry4C_hz0 hx hc) (lowGeometry4C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (9953 / 320000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry4C_hz3 hx hc) (lowGeometry4C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (1115403514428747 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry4C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (16061810607773957 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry4C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (231 / 250) (37 / 40) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry4C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry4C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry4C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (28901624629940789 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry4C_hz7 hx hc) (lowGeometry4C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (61025245845488703 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry4C_hz6 hx hc) (lowGeometry4C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (61025245845488703 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry4C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry4C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (180411 / 25000) (28897 / 4000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry4C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (28897 / 32000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry4C_hz13 hx hc) (lowGeometry4C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (61928277095488703 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry4C_hz12 hx hc) (lowGeometry4C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (61928277095488703 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry4C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry4C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (37 / 640000) (θ * x) := bmul (lowGeometry4C_hz0 hx hc) (lowGeometry4C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (26889534883721 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry4C_hz17 hx hc) (lowGeometry4C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (2074204807003243 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry4C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (298685492208467 / 10000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry4C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (298685492208467 / 10000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry4C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry4C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (75537 / 50000) (12099 / 8000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry4C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry4C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (16908866537356223 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry4C_hz22 hx hc) (lowGeometry4C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry4C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry4C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry4C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry4C_hz26 hx hc) (lowGeometry4C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry4C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 0 (17445185798566719 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry4C_hz24 hx hc) (lowGeometry4C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (10298685492208467 / 10000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry4C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B 1 (1060629228674251543 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry4C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (43 / 80) (570618525026747331 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry4C_hz2 hx hc) (lowGeometry4C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (43 / 80) (11761274216506281 / 20000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry4C_hz33 hx hc) (lowGeometry4C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (43 / 80) (11761274216506281 / 20000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry4C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry4C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (9701314507791533 / 10000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry4C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (470577515895432371 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry4C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (252935414793794899 / 500000000000000000) (269 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry4C_hz2 hx hc) (lowGeometry4C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (488425643789023079 / 1000000000000000000) (269 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry4C_hz38 hx hc) (lowGeometry4C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry4C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (231 / 500) (37 / 80) θ) : B (488425643789023079 / 1000000000000000000) (269 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry4C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry4C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (231 / 500) (37 / 80) θ) :
    OverlapGuard n θ lowCoreWindow (229971107 / 500000000) (626282771 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (30512623 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry4C_hz12 hx hc).2
  have hrp := (lowGeometry4C_hz16 hx hc).2
  have hbn := (lowGeometry4C_hz21 hx hc).2
  have hlo := (lowGeometry4C_hz40 hx hc).1
  have hhi := (lowGeometry4C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry5W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (37 / 80) (463 / 1000) θ := hc

theorem lowGeometry5W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry5W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (537 / 1000) (43 / 80) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry5W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (19869 / 80000) (19909 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry5W_hz0 hx hc) (lowGeometry5W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (19909 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry5W_hz3 hx hc) (lowGeometry5W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (5577437807811039 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry5W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (16732313423433117 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry5W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (37 / 40) (463 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry5W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry5W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry5W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (463 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry5W_hz7 hx hc) (lowGeometry5W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (28307313423433117 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry5W_hz6 hx hc) (lowGeometry5W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (28307313423433117 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry5W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry5W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (37 / 2) (463 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry5W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (463 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry5W_hz13 hx hc) (lowGeometry5W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (28886063423433117 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry5W_hz12 hx hc) (lowGeometry5W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (28886063423433117 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry5W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry5W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (463 / 8000000) (θ * x) := bmul (lowGeometry5W_hz0 hx hc) (lowGeometry5W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (107774674115457 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry5W_hz17 hx hc) (lowGeometry5W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (10381458188301729 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry5W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (31144374564905187 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry5W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (31144374564905187 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry5W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry5W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (37 / 10) (463 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry5W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry5W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (10352994735824027 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry5W_hz22 hx hc) (lowGeometry5W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry5W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry5W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry5W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry5W_hz26 hx hc) (lowGeometry5W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry5W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (21765924974601931 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry5W_hz24 hx hc) (lowGeometry5W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (531144374564905187 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry5W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (1128457386527777201 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry5W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (537 / 1000) (303272922629340123 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry5W_hz2 hx hc) (lowGeometry5W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (537 / 1000) (162519423801971027 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry5W_hz33 hx hc) (lowGeometry5W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (537 / 1000) (162519423801971027 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry5W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry5W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (468855625435094813 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry5W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (109912798751066963 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry5W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (472185383434583673 / 1000000000000000000) (43 / 80) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry5W_hz2 hx hc) (lowGeometry5W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (428653533485379811 / 1000000000000000000) (43 / 80) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry5W_hz38 hx hc) (lowGeometry5W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (428653533485379811 / 1000000000000000000) (43 / 80) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry5W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry5W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (37 / 80) (463 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (96063767 / 250000000) (366542141 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (56614627 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry5W_hz12 hx hc).2
  have hrp := (lowGeometry5W_hz16 hx hc).2
  have hbn := (lowGeometry5W_hz21 hx hc).2
  have hlo := (lowGeometry5W_hz40 hx hc).1
  have hhi := (lowGeometry5W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry5C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (37 / 80) (463 / 1000) θ := hc

theorem lowGeometry5C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry5C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (537 / 1000) (43 / 80) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry5C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (19869 / 80000) (19909 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry5C_hz0 hx hc) (lowGeometry5C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (19909 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry5C_hz3 hx hc) (lowGeometry5C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (5577437807811039 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry5C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (6425208354598317 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry5C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (37 / 40) (463 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry5C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry5C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry5C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (1157314785181629 / 40000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry5C_hz7 hx hc) (lowGeometry5C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (6105891140253231 / 100000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry5C_hz6 hx hc) (lowGeometry5C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (6105891140253231 / 100000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry5C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry5C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (28897 / 4000) (361603 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry5C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (361603 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry5C_hz13 hx hc) (lowGeometry5C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (6196291890253231 / 100000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry5C_hz12 hx hc) (lowGeometry5C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (6196291890253231 / 100000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry5C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry5C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (463 / 8000000) (θ * x) := bmul (lowGeometry5C_hz0 hx hc) (lowGeometry5C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (107774674115457 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry5C_hz17 hx hc) (lowGeometry5C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (10381458188301729 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry5C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (1494929979115449 / 50000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry5C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (1494929979115449 / 50000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry5C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry5C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (12099 / 8000) (151401 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry5C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry5C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (4231786598268071 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry5C_hz22 hx hc) (lowGeometry5C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry5C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry5C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry5C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry5C_hz26 hx hc) (lowGeometry5C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry5C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 0 (3492809091777899 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry5C_hz24 hx hc) (lowGeometry5C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (51494929979115449 / 50000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry5C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B 1 (1060691125421601207 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry5C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (537 / 1000) (570121479914110649 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry5C_hz2 hx hc) (lowGeometry5C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (537 / 1000) (36724095335812509 / 62500000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry5C_hz33 hx hc) (lowGeometry5C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (537 / 1000) (36724095335812509 / 62500000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry5C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry5C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (48505070020884551 / 50000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry5C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (470548363546182643 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry5C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (252684471224300079 / 500000000000000000) (43 / 80) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry5C_hz2 hx hc) (lowGeometry5C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (487904896989710663 / 1000000000000000000) (43 / 80) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry5C_hz38 hx hc) (lowGeometry5C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry5C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 80) (463 / 1000) θ) : B (487904896989710663 / 1000000000000000000) (43 / 80) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry5C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry5C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (37 / 80) (463 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (28714803 / 62500000) (125159189 / 200000000) ∧ radiusMinus n θ lowCoreWindow ≤ (1908091 / 31250000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry5C_hz12 hx hc).2
  have hrp := (lowGeometry5C_hz16 hx hc).2
  have hbn := (lowGeometry5C_hz21 hx hc).2
  have hlo := (lowGeometry5C_hz40 hx hc).1
  have hhi := (lowGeometry5C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry6W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (463 / 1000) (927 / 2000) θ := hc

theorem lowGeometry6W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry6W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (1073 / 2000) (537 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (496799 / 2000000) (497799 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry6W_hz0 hx hc) (lowGeometry6W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (497799 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry6W_hz3 hx hc) (lowGeometry6W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (5577852409305933 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry6W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (16733557227917799 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry6W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (463 / 500) (927 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry6W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry6W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry6W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (927 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry6W_hz7 hx hc) (lowGeometry6W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (28321057227917799 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry6W_hz6 hx hc) (lowGeometry6W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (28321057227917799 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry6W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry6W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (463 / 25) (927 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry6W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (927 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry6W_hz13 hx hc) (lowGeometry6W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (28900432227917799 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry6W_hz12 hx hc) (lowGeometry6W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (28900432227917799 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry6W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry6W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (927 / 16000000) (θ * x) := bmul (lowGeometry6W_hz0 hx hc) (lowGeometry6W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (53995806150979 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry6W_hz17 hx hc) (lowGeometry6W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (10391901284267379 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry6W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (31175703852802137 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry6W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (31175703852802137 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry6W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry6W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (463 / 125) (927 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry6W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry6W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (41456700302846103 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry6W_hz22 hx hc) (lowGeometry6W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry6W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry6W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry6W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry6W_hz26 hx hc) (lowGeometry6W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry6W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (21789430293149017 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry6W_hz24 hx hc) (lowGeometry6W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (531175703852802137 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry6W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (1128590513454079037 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry6W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (1073 / 2000) (606053105724840443 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry6W_hz2 hx hc) (lowGeometry6W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (1073 / 2000) (649631966311138477 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry6W_hz33 hx hc) (lowGeometry6W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (1073 / 2000) (649631966311138477 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry6W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry6W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (468824296147197863 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry6W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (43959244131583097 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry6W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (47168268953188663 / 100000000000000000) (537 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry6W_hz2 hx hc) (lowGeometry6W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (107025957236397149 / 250000000000000000) (537 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry6W_hz38 hx hc) (lowGeometry6W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (107025957236397149 / 250000000000000000) (537 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry6W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry6W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (463 / 1000) (927 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (383742529 / 1000000000) (366313529 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (113284229 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry6W_hz12 hx hc).2
  have hrp := (lowGeometry6W_hz16 hx hc).2
  have hbn := (lowGeometry6W_hz21 hx hc).2
  have hlo := (lowGeometry6W_hz40 hx hc).1
  have hhi := (lowGeometry6W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry6C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (463 / 1000) (927 / 2000) θ := hc

theorem lowGeometry6C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry6C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (1073 / 2000) (537 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (496799 / 2000000) (497799 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry6C_hz0 hx hc) (lowGeometry6C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (497799 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry6C_hz3 hx hc) (lowGeometry6C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (5577852409305933 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry6C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (1285137195104087 / 40000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry6C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (463 / 500) (927 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry6C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry6C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry6C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (28964114629140661 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry6C_hz7 hx hc) (lowGeometry6C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (15273136126685709 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry6C_hz6 hx hc) (lowGeometry6C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (15273136126685709 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry6C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry6C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (361603 / 50000) (723987 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry6C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (723987 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry6C_hz13 hx hc) (lowGeometry6C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (15499382064185709 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry6C_hz12 hx hc) (lowGeometry6C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (15499382064185709 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry6C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry6C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (927 / 16000000) (θ * x) := bmul (lowGeometry6C_hz0 hx hc) (lowGeometry6C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (53995806150979 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry6C_hz17 hx hc) (lowGeometry6C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (10391901284267379 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry6C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (7482168924672513 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry6C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (7482168924672513 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry6C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry6C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (151401 / 100000) (303129 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry6C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry6C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (3389085249757669 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry6C_hz22 hx hc) (lowGeometry6C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry6C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry6C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry6C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry6C_hz26 hx hc) (lowGeometry6C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry6C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 0 (1748290511921227 / 100000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry6C_hz24 hx hc) (lowGeometry6C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (257482168924672513 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry6C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B 1 (212150615405291493 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry6C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (1073 / 2000) (569624402363207659 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry6C_hz2 hx hc) (lowGeometry6C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (1073 / 2000) (587107307482419929 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry6C_hz33 hx hc) (lowGeometry6C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (1073 / 2000) (587107307482419929 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry6C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry6C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (242517831075327487 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry6C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (117629796778962157 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry6C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (504867087775305577 / 1000000000000000000) (537 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry6C_hz2 hx hc) (lowGeometry6C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (487384182656093307 / 1000000000000000000) (537 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry6C_hz38 hx hc) (lowGeometry6C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry6C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (463 / 1000) (927 / 2000) θ) : B (487384182656093307 / 1000000000000000000) (537 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry6C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry6C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (463 / 1000) (927 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (11473289 / 25000000) (156327257 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12218509 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry6C_hz12 hx hc).2
  have hrp := (lowGeometry6C_hz16 hx hc).2
  have hbn := (lowGeometry6C_hz21 hx hc).2
  have hlo := (lowGeometry6C_hz40 hx hc).1
  have hhi := (lowGeometry6C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry7W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (927 / 2000) (58 / 125) θ := hc

theorem lowGeometry7W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry7W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (67 / 125) (1073 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry7W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (62109 / 250000) (31117 / 125000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry7W_hz0 hx hc) (lowGeometry7W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (31117 / 1000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry7W_hz3 hx hc) (lowGeometry7W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (557826137788469 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry7W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (1673478413365407 / 25000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry7W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (927 / 1000) (116 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry7W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry7W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry7W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (29 / 625) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry7W_hz7 hx hc) (lowGeometry7W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (2833478413365407 / 25000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry7W_hz6 hx hc) (lowGeometry7W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (2833478413365407 / 25000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry7W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry7W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (927 / 50) (464 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry7W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (29 / 12500) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry7W_hz13 hx hc) (lowGeometry7W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (2891478413365407 / 25000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry7W_hz12 hx hc) (lowGeometry7W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (2891478413365407 / 25000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry7W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry7W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (29 / 500000) (θ * x) := bmul (lowGeometry7W_hz0 hx hc) (lowGeometry7W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (108208955223881 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry7W_hz17 hx hc) (lowGeometry7W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (10402353350270361 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry7W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (31207060050811083 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry7W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (31207060050811083 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry7W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry7W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (927 / 250) (464 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry7W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry7W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (41501421662396099 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry7W_hz22 hx hc) (lowGeometry7W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry7W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry7W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry7W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry7W_hz26 hx hc) (lowGeometry7W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry7W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (43625871223392207 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry7W_hz24 hx hc) (lowGeometry7W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (531207060050811083 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry7W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (1128723762591304049 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry7W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (67 / 125) (605560298630234623 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry7W_hz2 hx hc) (lowGeometry7W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (67 / 125) (64918616985362683 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry7W_hz33 hx hc) (lowGeometry7W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (67 / 125) (64918616985362683 / 100000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry7W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry7W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (468792939949188917 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry7W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (109883410273101923 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry7W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (94236012650212209 / 200000000000000000) (1073 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry7W_hz2 hx hc) (lowGeometry7W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (213777096013834419 / 500000000000000000) (1073 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry7W_hz38 hx hc) (lowGeometry7W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (213777096013834419 / 500000000000000000) (1073 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry7W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry7W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (927 / 2000) (58 / 125) θ) :
    OverlapGuard n θ lowWideWindow (191615063 / 500000000) (366084823 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (113339137 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry7W_hz12 hx hc).2
  have hrp := (lowGeometry7W_hz16 hx hc).2
  have hbn := (lowGeometry7W_hz21 hx hc).2
  have hlo := (lowGeometry7W_hz40 hx hc).1
  have hhi := (lowGeometry7W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry7C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (927 / 2000) (58 / 125) θ := hc

theorem lowGeometry7C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry7C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (67 / 125) (1073 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry7C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (62109 / 250000) (31117 / 125000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry7C_hz0 hx hc) (lowGeometry7C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (31117 / 1000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry7C_hz3 hx hc) (lowGeometry7C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (557826137788469 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry7C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (6426157107323163 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry7C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (927 / 1000) (116 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry7C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry7C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry7C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (28995359628740597 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry7C_hz7 hx hc) (lowGeometry7C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (15281536291339103 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry7C_hz6 hx hc) (lowGeometry7C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (15281536291339103 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry7C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry7C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (723987 / 100000) (22649 / 3125) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry7C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (22649 / 25000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry7C_hz13 hx hc) (lowGeometry7C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (15508026291339103 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry7C_hz12 hx hc) (lowGeometry7C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (15508026291339103 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry7C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry7C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (29 / 500000) (θ * x) := bmul (lowGeometry7C_hz0 hx hc) (lowGeometry7C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (108208955223881 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry7C_hz17 hx hc) (lowGeometry7C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (10402353350270361 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry7C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (374484720609733 / 12500000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry7C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (374484720609733 / 12500000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry7C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry7C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (303129 / 200000) (9483 / 6250) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry7C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry7C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (8481853052252203 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry7C_hz22 hx hc) (lowGeometry7C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry7C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry7C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry7C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry7C_hz26 hx hc) (lowGeometry7C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry7C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 0 (3500352955907009 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry7C_hz24 hx hc) (lowGeometry7C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (12874484720609733 / 12500000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry7C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B 1 (1060815083655766239 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry7C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (67 / 125) (142281823095329647 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry7C_hz2 hx hc) (lowGeometry7C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (67 / 125) (586629057160853633 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry7C_hz33 hx hc) (lowGeometry7C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (67 / 125) (586629057160853633 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry7C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry7C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (12125515279390267 / 12500000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry7C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (470489986530325839 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry7C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (504365265560509299 / 1000000000000000000) (1073 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry7C_hz2 hx hc) (lowGeometry7C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (243431750390487127 / 500000000000000000) (1073 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry7C_hz38 hx hc) (lowGeometry7C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry7C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (927 / 2000) (58 / 125) θ) : B (243431750390487127 / 500000000000000000) (1073 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry7C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry7C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (927 / 2000) (58 / 125) θ) :
    OverlapGuard n θ lowCoreWindow (458426349 / 1000000000) (624822019 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (30563073 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry7C_hz12 hx hc).2
  have hrp := (lowGeometry7C_hz16 hx hc).2
  have hbn := (lowGeometry7C_hz21 hx hc).2
  have hlo := (lowGeometry7C_hz40 hx hc).1
  have hhi := (lowGeometry7C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry8W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (58 / 125) (929 / 2000) θ := hc

theorem lowGeometry8W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry8W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (1071 / 2000) (67 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (31059 / 125000) (62243 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry8W_hz0 hx hc) (lowGeometry8W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (62243 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry8W_hz3 hx hc) (lowGeometry8W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (5578664714786147 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry8W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (16735994144358441 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry8W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (116 / 125) (929 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry8W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry8W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry8W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (929 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry8W_hz7 hx hc) (lowGeometry8W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (28348494144358441 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry8W_hz6 hx hc) (lowGeometry8W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (28348494144358441 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry8W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry8W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (464 / 25) (929 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry8W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (929 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry8W_hz13 hx hc) (lowGeometry8W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (28929119144358441 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry8W_hz12 hx hc) (lowGeometry8W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (28929119144358441 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry8W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry8W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (929 / 16000000) (θ * x) := bmul (lowGeometry8W_hz0 hx hc) (lowGeometry8W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (5421335200747 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry8W_hz17 hx hc) (lowGeometry8W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (1301601801717191 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry8W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (3904805405151573 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry8W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (3904805405151573 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry8W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry8W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (464 / 125) (929 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry8W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry8W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (8309228604389219 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry8W_hz22 hx hc) (lowGeometry8W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry8W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry8W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry8W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry8W_hz26 hx hc) (lowGeometry8W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry8W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (2183644093024319 / 50000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry8W_hz24 hx hc) (lowGeometry8W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (66404805405151573 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry8W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (1128857134309388177 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry8W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (1071 / 2000) (605067423989832063 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry8W_hz2 hx hc) (lowGeometry8W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (1071 / 2000) (648740305850318443 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry8W_hz33 hx hc) (lowGeometry8W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (1071 / 2000) (648740305850318443 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry8W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry8W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (58595194594848427 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry8W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (54934349273730469 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry8W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (235338752288661329 / 500000000000000000) (67 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry8W_hz2 hx hc) (lowGeometry8W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (213502311358418139 / 500000000000000000) (67 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry8W_hz38 hx hc) (lowGeometry8W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (213502311358418139 / 500000000000000000) (67 / 125) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry8W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry8W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (58 / 125) (929 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (19135893 / 50000000) (146342409 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (113393977 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry8W_hz12 hx hc).2
  have hrp := (lowGeometry8W_hz16 hx hc).2
  have hbn := (lowGeometry8W_hz21 hx hc).2
  have hlo := (lowGeometry8W_hz40 hx hc).1
  have hhi := (lowGeometry8W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry8C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (58 / 125) (929 / 2000) θ := hc

theorem lowGeometry8C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry8C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (1071 / 2000) (67 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (31059 / 125000) (62243 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry8C_hz0 hx hc) (lowGeometry8C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (62243 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry8C_hz3 hx hc) (lowGeometry8C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (5578664714786147 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry8C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (32133108757168207 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry8C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (116 / 125) (929 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry8C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry8C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry8C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (29026604628340533 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry8C_hz7 hx hc) (lowGeometry8C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (3057985669275437 / 50000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry8C_hz6 hx hc) (lowGeometry8C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (3057985669275437 / 50000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry8C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry8C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (22649 / 3125) (725549 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry8C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (725549 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry8C_hz13 hx hc) (lowGeometry8C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (3103332481775437 / 50000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry8C_hz12 hx hc) (lowGeometry8C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (3103332481775437 / 50000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry8C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry8C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (929 / 16000000) (θ * x) := bmul (lowGeometry8C_hz0 hx hc) (lowGeometry8C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (5421335200747 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry8C_hz17 hx hc) (lowGeometry8C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (1301601801717191 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry8C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (29988905511564081 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry8C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (29988905511564081 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry8C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry8C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (9483 / 6250) (303783 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry8C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry8C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (16981985960220467 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry8C_hz22 hx hc) (lowGeometry8C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry8C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry8C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry8C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry8C_hz26 hx hc) (lowGeometry8C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry8C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 0 (876031221992891 / 50000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry8C_hz24 hx hc) (lowGeometry8C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (1029988905511564081 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry8C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B 1 (1060877145476909681 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry8C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (1071 / 2000) (56863014997562359 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry8C_hz2 hx hc) (lowGeometry8C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (1071 / 2000) (58615077441548141 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry8C_hz33 hx hc) (lowGeometry8C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (1071 / 2000) (58615077441548141 / 100000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry8C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry8C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (970011094488435919 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry8C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (235230380857663339 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry8C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (62982934474639359 / 125000000000000000) (67 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry8C_hz2 hx hc) (lowGeometry8C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (121585712839314263 / 250000000000000000) (67 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry8C_hz38 hx hc) (lowGeometry8C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry8C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (58 / 125) (929 / 2000) θ) : B (121585712839314263 / 250000000000000000) (67 / 125) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry8C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry8C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (58 / 125) (929 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (91584243 / 200000000) (15608373 / 25000000) ∧ radiusMinus n θ lowCoreWindow ≤ (30579857 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry8C_hz12 hx hc).2
  have hrp := (lowGeometry8C_hz16 hx hc).2
  have hbn := (lowGeometry8C_hz21 hx hc).2
  have hlo := (lowGeometry8C_hz40 hx hc).1
  have hhi := (lowGeometry8C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry9W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (929 / 2000) (93 / 200) θ := hc

theorem lowGeometry9W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry9W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (107 / 200) (1071 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry9W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (99403 / 400000) (99603 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry9W_hz0 hx hc) (lowGeometry9W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (99603 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry9W_hz3 hx hc) (lowGeometry9W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (2789531210615863 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry9W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (8368593631847589 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry9W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (929 / 1000) (93 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry9W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry9W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry9W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (93 / 2000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry9W_hz7 hx hc) (lowGeometry9W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (14181093631847589 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry9W_hz6 hx hc) (lowGeometry9W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (14181093631847589 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry9W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry9W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (929 / 50) (93 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry9W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (93 / 40000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry9W_hz13 hx hc) (lowGeometry9W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (14471718631847589 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry9W_hz12 hx hc) (lowGeometry9W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (14471718631847589 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry9W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry9W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (93 / 1600000) (θ * x) := bmul (lowGeometry9W_hz0 hx hc) (lowGeometry9W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (21728971962617 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry9W_hz17 hx hc) (lowGeometry9W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (10423284502165573 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry9W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (31269853506496719 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry9W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (31269853506496719 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry9W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry9W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (929 / 250) (93 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry9W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry9W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (41590864381496091 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry9W_hz22 hx hc) (lowGeometry9W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry9W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry9W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry9W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry9W_hz26 hx hc) (lowGeometry9W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry9W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (43719892497580553 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry9W_hz24 hx hc) (lowGeometry9W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (531269853506496719 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry9W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (1128990628979257937 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry9W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (107 / 200) (302287240909196313 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry9W_hz2 hx hc) (lowGeometry9W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (107 / 200) (648294374315973179 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry9W_hz33 hx hc) (lowGeometry9W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (107 / 200) (648294374315973179 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry9W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry9W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (468730146493503281 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry9W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (109853975115910523 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry9W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (235087506748048519 / 500000000000000000) (1071 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry9W_hz2 hx hc) (lowGeometry9W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (85291024199703297 / 200000000000000000) (1071 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry9W_hz38 hx hc) (lowGeometry9W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (85291024199703297 / 200000000000000000) (1071 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry9W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry9W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (929 / 2000) (93 / 200) θ) :
    OverlapGuard n θ lowWideWindow (38220573 / 100000000) (146250851 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (90759 / 800000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry9W_hz12 hx hc).2
  have hrp := (lowGeometry9W_hz16 hx hc).2
  have hbn := (lowGeometry9W_hz21 hx hc).2
  have hlo := (lowGeometry9W_hz40 hx hc).1
  have hhi := (lowGeometry9W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry9C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (929 / 2000) (93 / 200) θ := hc

theorem lowGeometry9C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry9C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (107 / 200) (1071 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry9C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (99403 / 400000) (99603 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry9C_hz0 hx hc) (lowGeometry9C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (99603 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry9C_hz3 hx hc) (lowGeometry9C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (2789531210615863 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry9C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (16067699773147371 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry9C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (929 / 1000) (93 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry9C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry9C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry9C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (29057849627940469 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry9C_hz7 hx hc) (lowGeometry9C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (61193249174235211 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry9C_hz6 hx hc) (lowGeometry9C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (61193249174235211 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry9C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry9C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (725549 / 100000) (72633 / 10000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry9C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (72633 / 80000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry9C_hz13 hx hc) (lowGeometry9C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (62101161674235211 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry9C_hz12 hx hc) (lowGeometry9C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (62101161674235211 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry9C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry9C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (93 / 1600000) (θ * x) := bmul (lowGeometry9C_hz0 hx hc) (lowGeometry9C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (21728971962617 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry9C_hz17 hx hc) (lowGeometry9C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (10423284502165573 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry9C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (30019059366236851 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry9C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (30019059366236851 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry9C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry9C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (303783 / 200000) (30411 / 20000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry9C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry9C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (17000265815936527 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry9C_hz22 hx hc) (lowGeometry9C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry9C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry9C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry9C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry9C_hz26 hx hc) (lowGeometry9C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry9C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 0 (8769742050090297 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry9C_hz24 hx hc) (lowGeometry9C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (1030019059366236851 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry9C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B 1 (212187852531541471 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry9C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (107 / 200) (568132975153202289 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry9C_hz2 hx hc) (lowGeometry9C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (107 / 200) (585672459253382883 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry9C_hz33 hx hc) (lowGeometry9C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (107 / 200) (585672459253382883 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry9C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry9C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (969980940633763149 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry9C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (18817260503855199 / 20000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry9C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (503361718478126573 / 1000000000000000000) (1071 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry9C_hz2 hx hc) (lowGeometry9C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (485822234377945979 / 1000000000000000000) (1071 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry9C_hz38 hx hc) (lowGeometry9C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry9C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (929 / 2000) (93 / 200) θ) : B (485822234377945979 / 1000000000000000000) (1071 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry9C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry9C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (929 / 2000) (93 / 200) θ) :
    OverlapGuard n θ lowCoreWindow (457416159 / 1000000000) (623847729 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (244773 / 4000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry9C_hz12 hx hc).2
  have hrp := (lowGeometry9C_hz16 hx hc).2
  have hbn := (lowGeometry9C_hz21 hx hc).2
  have hlo := (lowGeometry9C_hz40 hx hc).1
  have hhi := (lowGeometry9C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry10W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (93 / 200) (931 / 2000) θ := hc

theorem lowGeometry10W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry10W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (1069 / 2000) (107 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (99417 / 400000) (99617 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry10W_hz0 hx hc) (lowGeometry10W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (99617 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry10W_hz3 hx hc) (lowGeometry10W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (5579454498425451 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry10W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (16738363495276353 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry10W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (93 / 100) (931 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry10W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry10W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry10W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (931 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry10W_hz7 hx hc) (lowGeometry10W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (28375863495276353 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry10W_hz6 hx hc) (lowGeometry10W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (28375863495276353 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry10W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry10W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (93 / 5) (931 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry10W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (931 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry10W_hz13 hx hc) (lowGeometry10W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (28957738495276353 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry10W_hz12 hx hc) (lowGeometry10W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (28957738495276353 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry10W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry10W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (931 / 16000000) (θ * x) := bmul (lowGeometry10W_hz0 hx hc) (lowGeometry10W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (27215855940131 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry10W_hz17 hx hc) (lowGeometry10W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (10433763643121499 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry10W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (31301290929364497 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry10W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (31301290929364497 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry10W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry10W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (93 / 25) (931 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry10W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry10W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (41635585741046087 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry10W_hz22 hx hc) (lowGeometry10W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry10W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry10W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry10W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry10W_hz26 hx hc) (lowGeometry10W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry10W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (1750676125386989 / 40000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry10W_hz24 hx hc) (lowGeometry10W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (531301290929364497 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry10W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (1129124246972836853 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry10W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (1069 / 2000) (604081472130467717 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry10W_hz2 hx hc) (lowGeometry10W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (1069 / 2000) (323924187632571221 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry10W_hz33 hx hc) (lowGeometry10W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (1069 / 2000) (323924187632571221 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry10W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry10W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (468698709070635503 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry10W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (219678479884480219 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry10W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (117418147498254677 / 250000000000000000) (107 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry10W_hz2 hx hc) (lowGeometry10W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (425905686858343983 / 1000000000000000000) (107 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry10W_hz38 hx hc) (lowGeometry10W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (425905686858343983 / 1000000000000000000) (107 / 200) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry10W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry10W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (93 / 200) (931 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (381693737 / 1000000000) (730796277 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (56751727 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry10W_hz12 hx hc).2
  have hrp := (lowGeometry10W_hz16 hx hc).2
  have hbn := (lowGeometry10W_hz21 hx hc).2
  have hlo := (lowGeometry10W_hz40 hx hc).1
  have hhi := (lowGeometry10W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry10C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (93 / 200) (931 / 2000) θ := hc

theorem lowGeometry10C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry10C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (1069 / 2000) (107 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (99417 / 400000) (99617 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry10C_hz0 hx hc) (lowGeometry10C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (99617 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry10C_hz3 hx hc) (lowGeometry10C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (5579454498425451 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry10C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (16068828955465299 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry10C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (93 / 100) (931 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry10C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry10C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry10C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (5817818925508081 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry10C_hz7 hx hc) (lowGeometry10C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (61226752538471003 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry10C_hz6 hx hc) (lowGeometry10C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (61226752538471003 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry10C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry10C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (72633 / 10000) (727111 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry10C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (727111 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry10C_hz13 hx hc) (lowGeometry10C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (62135641288471003 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry10C_hz12 hx hc) (lowGeometry10C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (62135641288471003 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry10C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry10C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (931 / 16000000) (θ * x) := bmul (lowGeometry10C_hz0 hx hc) (lowGeometry10C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (27215855940131 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry10C_hz17 hx hc) (lowGeometry10C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (10433763643121499 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry10C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (15024619646094959 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry10C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (15024619646094959 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry10C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry10C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (30411 / 20000) (304437 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry10C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry10C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (4254636417913147 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry10C_hz22 hx hc) (lowGeometry10C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry10C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry10C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry10C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry10C_hz26 hx hc) (lowGeometry10C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry10C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 0 (17558343760503369 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry10C_hz24 hx hc) (lowGeometry10C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (515024619646094959 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry10C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B 1 (1061001435366419127 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry10C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (1069 / 2000) (567635767921034233 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry10C_hz2 hx hc) (lowGeometry10C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (1069 / 2000) (292597055840768801 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry10C_hz33 hx hc) (lowGeometry10C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (1069 / 2000) (292597055840768801 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry10C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry10C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (484975380353905041 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry10C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (470402239098829727 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry10C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (251429996798324489 / 500000000000000000) (107 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry10C_hz2 hx hc) (lowGeometry10C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (485301649836145609 / 1000000000000000000) (107 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry10C_hz38 hx hc) (lowGeometry10C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry10C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (93 / 200) (931 / 2000) θ) : B (485301649836145609 / 1000000000000000000) (107 / 200) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry10C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry10C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (93 / 200) (931 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (22845559 / 50000000) (9740007 / 15625000) ∧ radiusMinus n θ lowCoreWindow ≤ (61226753 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry10C_hz12 hx hc).2
  have hrp := (lowGeometry10C_hz16 hx hc).2
  have hbn := (lowGeometry10C_hz21 hx hc).2
  have hlo := (lowGeometry10C_hz40 hx hc).1
  have hhi := (lowGeometry10C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry11W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (931 / 2000) (233 / 500) θ := hc

theorem lowGeometry11W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry11W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (267 / 500) (1069 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry11W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (248577 / 1000000) (249077 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry11W_hz0 hx hc) (lowGeometry11W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (249077 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry11W_hz3 hx hc) (lowGeometry11W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (1394960236888493 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry11W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (4184880710665479 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry11W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (931 / 1000) (233 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry11W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry11W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry11W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (233 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry11W_hz7 hx hc) (lowGeometry11W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (7097380710665479 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry11W_hz6 hx hc) (lowGeometry11W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (7097380710665479 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry11W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry11W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (931 / 50) (466 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry11W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (233 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry11W_hz13 hx hc) (lowGeometry11W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (7243005710665479 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry11W_hz12 hx hc) (lowGeometry11W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (7243005710665479 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry11W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry11W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (233 / 4000000) (θ * x) := bmul (lowGeometry11W_hz0 hx hc) (lowGeometry11W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (54541198501873 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry11W_hz17 hx hc) (lowGeometry11W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (5222125932121563 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry11W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (15666377796364689 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry11W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (15666377796364689 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry11W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry11W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (931 / 250) (466 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry11W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry11W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (20840153550298041 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry11W_hz22 hx hc) (lowGeometry11W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry11W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry11W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry11W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry11W_hz26 hx hc) (lowGeometry11W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry11W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (43813913771768897 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry11W_hz24 hx hc) (lowGeometry11W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (265666377796364689 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry11W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (1129257988663052369 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry11W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (267 / 500) (150897098735100373 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry11W_hz2 hx hc) (lowGeometry11W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (267 / 500) (647402308712170389 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry11W_hz33 hx hc) (lowGeometry11W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (267 / 500) (647402308712170389 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry11W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry11W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (234333622203635311 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry11W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (13728061623769021 / 15625000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry11W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (469170234053930061 / 1000000000000000000) (1069 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry11W_hz2 hx hc) (lowGeometry11W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (106339080070540291 / 250000000000000000) (1069 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry11W_hz38 hx hc) (lowGeometry11W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (106339080070540291 / 250000000000000000) (1069 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry11W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry11W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (931 / 2000) (233 / 500) θ) :
    OverlapGuard n θ lowWideWindow (381181879 / 1000000000) (730338111 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (28389523 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry11W_hz12 hx hc).2
  have hrp := (lowGeometry11W_hz16 hx hc).2
  have hbn := (lowGeometry11W_hz21 hx hc).2
  have hlo := (lowGeometry11W_hz40 hx hc).1
  have hhi := (lowGeometry11W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry11C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (931 / 2000) (233 / 500) θ := hc

theorem lowGeometry11C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry11C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (267 / 500) (1069 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry11C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (248577 / 1000000) (249077 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry11C_hz0 hx hc) (lowGeometry11C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (249077 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry11C_hz3 hx hc) (lowGeometry11C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (1394960236888493 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry11C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (32139883857910879 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry11C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (931 / 1000) (233 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry11C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry11C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry11C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (29120339627140341 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry11C_hz7 hx hc) (lowGeometry11C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (3063011174252561 / 50000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry11C_hz6 hx hc) (lowGeometry11C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (3063011174252561 / 50000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry11C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry11C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (727111 / 100000) (181973 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry11C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (181973 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry11C_hz13 hx hc) (lowGeometry11C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (3108504424252561 / 50000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry11C_hz12 hx hc) (lowGeometry11C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (3108504424252561 / 50000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry11C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry11C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (233 / 4000000) (θ * x) := bmul (lowGeometry11C_hz0 hx hc) (lowGeometry11C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (54541198501873 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry11C_hz17 hx hc) (lowGeometry11C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (5222125932121563 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry11C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (30079445369020203 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry11C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (30079445369020203 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry11C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry11C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (304437 / 200000) (76191 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry11C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry11C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (17036825527368649 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry11C_hz22 hx hc) (lowGeometry11C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry11C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry11C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry11C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry11C_hz26 hx hc) (lowGeometry11C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry11C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 0 (549287606900817 / 31250000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry11C_hz24 hx hc) (lowGeometry11C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (1030079445369020203 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry11C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B 1 (1061063663771748277 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry11C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (267 / 500) (113427705657199891 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry11C_hz2 hx hc) (lowGeometry11C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (267 / 500) (584715731706825599 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry11C_hz33 hx hc) (lowGeometry11C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (267 / 500) (584715731706825599 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry11C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry11C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (969920554630979797 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry11C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (117593235286958433 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry11C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (20094332045835457 / 40000000000000000) (1069 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry11C_hz2 hx hc) (lowGeometry11C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (484781097725060281 / 1000000000000000000) (1069 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry11C_hz38 hx hc) (lowGeometry11C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry11C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (931 / 2000) (233 / 500) θ) : B (484781097725060281 / 1000000000000000000) (1069 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry11C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry11C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (931 / 2000) (233 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (228203139 / 500000000) (155718269 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (957191 / 15625000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry11C_hz12 hx hc).2
  have hrp := (lowGeometry11C_hz16 hx hc).2
  have hbn := (lowGeometry11C_hz21 hx hc).2
  have hlo := (lowGeometry11C_hz40 hx hc).1
  have hhi := (lowGeometry11C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry12W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (233 / 500) (933 / 2000) θ := hc

theorem lowGeometry12W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry12W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (1067 / 2000) (267 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (248611 / 1000000) (249111 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry12W_hz0 hx hc) (lowGeometry12W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (249111 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry12W_hz3 hx hc) (lowGeometry12W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (2790110884893287 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry12W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (8370332654679861 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry12W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (233 / 250) (933 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry12W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry12W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (933 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry12W_hz7 hx hc) (lowGeometry12W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (14201582654679861 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry12W_hz6 hx hc) (lowGeometry12W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (14201582654679861 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry12W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry12W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (466 / 25) (933 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry12W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (933 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry12W_hz13 hx hc) (lowGeometry12W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (14493145154679861 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry12W_hz12 hx hc) (lowGeometry12W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (14493145154679861 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry12W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry12W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (933 / 16000000) (θ * x) := bmul (lowGeometry12W_hz0 hx hc) (lowGeometry12W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (54650890346767 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry12W_hz17 hx hc) (lowGeometry12W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (10454749193239119 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry12W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (31364247579717357 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry12W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (31364247579717357 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry12W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry12W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (466 / 125) (933 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry12W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry12W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (20862514230073039 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry12W_hz22 hx hc) (lowGeometry12W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry12W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry12W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry12W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry12W_hz26 hx hc) (lowGeometry12W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry12W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (4386092440886307 / 100000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry12W_hz24 hx hc) (lowGeometry12W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (531364247579717357 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry12W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (1129391854423836653 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry12W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (1067 / 2000) (603095250262328773 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry12W_hz2 hx hc) (lowGeometry12W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (1067 / 2000) (646956174671191843 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry12W_hz33 hx hc) (lowGeometry12W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (1067 / 2000) (646956174671191843 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry12W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry12W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (468635752420282643 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry12W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (219619468446524449 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry12W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (234333972832441587 / 500000000000000000) (267 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry12W_hz2 hx hc) (lowGeometry12W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (53100877657002513 / 125000000000000000) (267 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry12W_hz38 hx hc) (lowGeometry12W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (53100877657002513 / 125000000000000000) (267 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry12W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry12W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (233 / 500) (933 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (190335079 / 500000000) (729879757 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (56806331 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry12W_hz12 hx hc).2
  have hrp := (lowGeometry12W_hz16 hx hc).2
  have hbn := (lowGeometry12W_hz21 hx hc).2
  have hlo := (lowGeometry12W_hz40 hx hc).1
  have hhi := (lowGeometry12W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry12C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (233 / 500) (933 / 2000) θ := hc

theorem lowGeometry12C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry12C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (1067 / 2000) (267 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (248611 / 1000000) (249111 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry12C_hz0 hx hc) (lowGeometry12C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (249111 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry12C_hz3 hx hc) (lowGeometry12C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (2790110884893287 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry12C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (32142077393970667 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry12C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (233 / 250) (933 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry12C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry12C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (29151584626740277 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry12C_hz7 hx hc) (lowGeometry12C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1915426938147217 / 31250000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry12C_hz6 hx hc) (lowGeometry12C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1915426938147217 / 31250000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry12C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry12C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (181973 / 25000) (728673 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry12C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (728673 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry12C_hz13 hx hc) (lowGeometry12C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1943890727209717 / 31250000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry12C_hz12 hx hc) (lowGeometry12C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1943890727209717 / 31250000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry12C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry12C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (933 / 16000000) (θ * x) := bmul (lowGeometry12C_hz0 hx hc) (lowGeometry12C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (54650890346767 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry12C_hz17 hx hc) (lowGeometry12C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (10454749193239119 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry12C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (30109677676528663 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry12C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (30109677676528663 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry12C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry12C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (76191 / 50000) (305091 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry12C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry12C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (1705510538308471 / 100000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry12C_hz22 hx hc) (lowGeometry12C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry12C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry12C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry12C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry12C_hz26 hx hc) (lowGeometry12C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry12C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 0 (17596063081148919 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry12C_hz24 hx hc) (lowGeometry12C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (1030109677676528663 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry12C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B 1 (42445037921713671 / 40000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry12C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (1067 / 2000) (141660314063719377 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry12C_hz2 hx hc) (lowGeometry12C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (1067 / 2000) (584237319336026427 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry12C_hz33 hx hc) (lowGeometry12C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (1067 / 2000) (584237319336026427 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry12C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry12C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (969890322323471337 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry12C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (470343618668363561 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry12C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (501856641119143919 / 1000000000000000000) (267 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry12C_hz2 hx hc) (lowGeometry12C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (96852115607599 / 200000000000000) (267 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry12C_hz38 hx hc) (lowGeometry12C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry12C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (233 / 500) (933 / 2000) θ) : B (96852115607599 / 200000000000000) (267 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry12C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry12C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (233 / 500) (933 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (227950727 / 500000000) (622385613 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61293663 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry12C_hz12 hx hc).2
  have hrp := (lowGeometry12C_hz16 hx hc).2
  have hbn := (lowGeometry12C_hz21 hx hc).2
  have hlo := (lowGeometry12C_hz40 hx hc).1
  have hhi := (lowGeometry12C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry13W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (933 / 2000) (467 / 1000) θ := hc

theorem lowGeometry13W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry13W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (533 / 1000) (1067 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry13W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (497289 / 2000000) (498289 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry13W_hz0 hx hc) (lowGeometry13W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (498289 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry13W_hz3 hx hc) (lowGeometry13W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (1395149241568801 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry13W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (4185447724706403 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry13W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (933 / 1000) (467 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry13W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry13W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry13W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (467 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry13W_hz7 hx hc) (lowGeometry13W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (7104197724706403 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry13W_hz6 hx hc) (lowGeometry13W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (7104197724706403 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry13W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry13W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (933 / 50) (467 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry13W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (467 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry13W_hz13 hx hc) (lowGeometry13W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (7250135224706403 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry13W_hz12 hx hc) (lowGeometry13W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (7250135224706403 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry13W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry13W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (467 / 8000000) (θ * x) := bmul (lowGeometry13W_hz0 hx hc) (lowGeometry13W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (109521575984991 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry13W_hz17 hx hc) (lowGeometry13W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (2093051131577927 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry13W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (6279153394733781 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry13W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (6279153394733781 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry13W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry13W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (933 / 250) (467 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry13W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry13W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (20884874909848037 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry13W_hz22 hx hc) (lowGeometry13W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry13W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry13W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry13W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry13W_hz26 hx hc) (lowGeometry13W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry13W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (43907935045957243 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry13W_hz24 hx hc) (lowGeometry13W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (106279153394733781 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry13W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (1129525844630135297 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry13W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (533 / 1000) (602602038110177181 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry13W_hz2 hx hc) (lowGeometry13W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (533 / 1000) (80813746644516803 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry13W_hz33 hx hc) (lowGeometry13W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (533 / 1000) (80813746644516803 / 125000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry13W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry13W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (93720846605266219 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry13W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (109794963605098007 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry13W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (468165724812137901 / 1000000000000000000) (1067 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry13W_hz2 hx hc) (lowGeometry13W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (212128894883090329 / 500000000000000000) (1067 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry13W_hz38 hx hc) (lowGeometry13W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (212128894883090329 / 500000000000000000) (1067 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry13W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry13W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (933 / 2000) (467 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (95039643 / 250000000) (364710607 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (28416791 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry13W_hz12 hx hc).2
  have hrp := (lowGeometry13W_hz16 hx hc).2
  have hbn := (lowGeometry13W_hz21 hx hc).2
  have hlo := (lowGeometry13W_hz40 hx hc).1
  have hhi := (lowGeometry13W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry13C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (933 / 2000) (467 / 1000) θ := hc

theorem lowGeometry13C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry13C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (533 / 1000) (1067 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry13C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (497289 / 2000000) (498289 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry13C_hz0 hx hc) (lowGeometry13C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (498289 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry13C_hz3 hx hc) (lowGeometry13C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (1395149241568801 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry13C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (4018029815718147 / 125000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry13C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (933 / 1000) (467 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry13C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry13C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry13C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (29182829626340213 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry13C_hz7 hx hc) (lowGeometry13C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (61327068152085389 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry13C_hz6 hx hc) (lowGeometry13C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (61327068152085389 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry13C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry13C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (728673 / 100000) (364727 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry13C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (364727 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry13C_hz13 hx hc) (lowGeometry13C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (62238885652085389 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry13C_hz12 hx hc) (lowGeometry13C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (62238885652085389 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry13C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry13C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (467 / 8000000) (θ * x) := bmul (lowGeometry13C_hz0 hx hc) (lowGeometry13C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (109521575984991 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry13C_hz17 hx hc) (lowGeometry13C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (2093051131577927 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry13C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (30139936294722149 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry13C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (30139936294722149 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry13C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry13C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (305091 / 200000) (152709 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry13C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry13C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (17073385238800771 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry13C_hz22 hx hc) (lowGeometry13C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry13C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry13C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry13C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry13C_hz26 hx hc) (lowGeometry13C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry13C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 0 (8807461370735847 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry13C_hz24 hx hc) (lowGeometry13C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (1030139936294722149 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry13C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B 1 (8290533502728861 / 7812500000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry13C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (533 / 1000) (28307197591717423 / 50000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry13C_hz2 hx hc) (lowGeometry13C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (533 / 1000) (291879437287910077 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry13C_hz33 hx hc) (lowGeometry13C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (533 / 1000) (291879437287910077 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry13C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry13C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (969860063705277851 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry13C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (940628543170405611 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry13C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (50135501350982619 / 100000000000000000) (1067 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry13C_hz2 hx hc) (lowGeometry13C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (7558438918255539 / 15625000000000000) (1067 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry13C_hz38 hx hc) (lowGeometry13C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry13C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (933 / 2000) (467 / 1000) θ) : B (7558438918255539 / 15625000000000000) (1067 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry13C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry13C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (933 / 2000) (467 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (455396707 / 1000000000) (31094903 / 50000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61327069 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry13C_hz12 hx hc).2
  have hrp := (lowGeometry13C_hz16 hx hc).2
  have hbn := (lowGeometry13C_hz21 hx hc).2
  have hlo := (lowGeometry13C_hz40 hx hc).1
  have hhi := (lowGeometry13C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry14W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (467 / 1000) (187 / 400) θ := hc

theorem lowGeometry14W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry14W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (213 / 400) (533 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (99471 / 400000) (99671 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry14W_hz0 hx hc) (lowGeometry14W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (99671 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry14W_hz3 hx hc) (lowGeometry14W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (69762081726931 / 12500000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry14W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (209286245180793 / 3125000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry14W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (467 / 500) (187 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry14W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry14W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (187 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry14W_hz7 hx hc) (lowGeometry14W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (355379995180793 / 3125000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry14W_hz6 hx hc) (lowGeometry14W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (355379995180793 / 3125000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry14W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry14W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (467 / 25) (187 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry14W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (187 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry14W_hz13 hx hc) (lowGeometry14W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (362684682680793 / 3125000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry14W_hz12 hx hc) (lowGeometry14W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (362684682680793 / 3125000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry14W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry14W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (187 / 3200000) (θ * x) := bmul (lowGeometry14W_hz0 hx hc) (lowGeometry14W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (109741784037559 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry14W_hz17 hx hc) (lowGeometry14W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (10475771286046627 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry14W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (31427313858139881 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry14W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (31427313858139881 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry14W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry14W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (467 / 125) (187 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry14W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry14W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (4181447117924607 / 100000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry14W_hz22 hx hc) (lowGeometry14W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry14W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry14W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry14W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry14W_hz26 hx hc) (lowGeometry14W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry14W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (5494368210381427 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry14W_hz24 hx hc) (lowGeometry14W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (531427313858139881 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry14W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (1129659959657911649 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry14W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (213 / 400) (602108758497666909 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry14W_hz2 hx hc) (lowGeometry14W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (213 / 400) (25842548167228733 / 40000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry14W_hz33 hx hc) (lowGeometry14W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (213 / 400) (25842548167228733 / 40000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry14W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry14W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (468572686141860119 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry14W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (4391207243963963 / 5000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry14W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (467663571482162059 / 1000000000000000000) (533 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry14W_hz2 hx hc) (lowGeometry14W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (423708625799110643 / 1000000000000000000) (533 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry14W_hz38 hx hc) (lowGeometry14W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (423708625799110643 / 1000000000000000000) (533 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry14W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry14W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (467 / 1000) (187 / 400) θ) :
    OverlapGuard n θ lowWideWindow (189823561 / 500000000) (728962483 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (113721599 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry14W_hz12 hx hc).2
  have hrp := (lowGeometry14W_hz16 hx hc).2
  have hbn := (lowGeometry14W_hz21 hx hc).2
  have hlo := (lowGeometry14W_hz40 hx hc).1
  have hhi := (lowGeometry14W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry14C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (467 / 1000) (187 / 400) θ := hc

theorem lowGeometry14C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry14C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (213 / 400) (533 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (99471 / 400000) (99671 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry14C_hz0 hx hc) (lowGeometry14C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (99671 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry14C_hz3 hx hc) (lowGeometry14C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (69762081726931 / 12500000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry14C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (6429273451953961 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry14C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (467 / 500) (187 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry14C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry14C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (29214074625940149 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry14C_hz7 hx hc) (lowGeometry14C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (30680220942854977 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry14C_hz6 hx hc) (lowGeometry14C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (30680220942854977 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry14C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry14C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (364727 / 50000) (146047 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry14C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (146047 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry14C_hz13 hx hc) (lowGeometry14C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (31136617817854977 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry14C_hz12 hx hc) (lowGeometry14C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (31136617817854977 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry14C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry14C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (187 / 3200000) (θ * x) := bmul (lowGeometry14C_hz0 hx hc) (lowGeometry14C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (109741784037559 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry14C_hz17 hx hc) (lowGeometry14C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (10475771286046627 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry14C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (15085110651907143 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry14C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (15085110651907143 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry14C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry14C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (152709 / 100000) (61149 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry14C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry14C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (17091665094516831 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry14C_hz22 hx hc) (lowGeometry14C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry14C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry14C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry14C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry14C_hz26 hx hc) (lowGeometry14C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry14C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 0 (4408445600448617 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry14C_hz24 hx hc) (lowGeometry14C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (515085110651907143 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry14C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B 1 (530625342430574851 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry14C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (213 / 400) (70705826878874099 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry14C_hz2 hx hc) (lowGeometry14C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (213 / 400) (29164019871639363 / 50000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry14C_hz33 hx hc) (lowGeometry14C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (213 / 400) (29164019871639363 / 50000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry14C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry14C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (484914889348092857 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry14C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (940569799645892557 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry14C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (250426709155718893 / 500000000000000000) (533 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry14C_hz2 hx hc) (lowGeometry14C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (241609817954821659 / 500000000000000000) (533 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry14C_hz38 hx hc) (lowGeometry14C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry14C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (467 / 1000) (187 / 400) θ) : B (241609817954821659 / 500000000000000000) (533 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry14C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry14C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (467 / 1000) (187 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (113723009 / 250000000) (38838151 / 62500000) ∧ radiusMinus n θ lowCoreWindow ≤ (30680221 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry14C_hz12 hx hc).2
  have hrp := (lowGeometry14C_hz16 hx hc).2
  have hbn := (lowGeometry14C_hz21 hx hc).2
  have hlo := (lowGeometry14C_hz40 hx hc).1
  have hhi := (lowGeometry14C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry15W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (187 / 400) (117 / 250) θ := hc

theorem lowGeometry15W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry15W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (133 / 250) (213 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry15W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (24871 / 100000) (24921 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry15W_hz0 hx hc) (lowGeometry15W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (24921 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry15W_hz3 hx hc) (lowGeometry15W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (2790665243270859 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry15W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (8371995729812577 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry15W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (187 / 200) (117 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry15W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry15W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry15W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (117 / 2500) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry15W_hz7 hx hc) (lowGeometry15W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (14221995729812577 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry15W_hz6 hx hc) (lowGeometry15W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (14221995729812577 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry15W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry15W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (187 / 10) (468 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry15W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (117 / 50000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry15W_hz13 hx hc) (lowGeometry15W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (14514495729812577 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry15W_hz12 hx hc) (lowGeometry15W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (14514495729812577 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry15W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry15W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (117 / 2000000) (θ * x) := bmul (lowGeometry15W_hz0 hx hc) (lowGeometry15W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (54981203007519 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry15W_hz17 hx hc) (lowGeometry15W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (10486296105634153 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry15W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (31458888316902459 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry15W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (31458888316902459 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry15W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry15W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (187 / 50) (468 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry15W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry15W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (20929596269398033 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry15W_hz22 hx hc) (lowGeometry15W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry15W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry15W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry15W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry15W_hz26 hx hc) (lowGeometry15W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry15W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (44001956320145589 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry15W_hz24 hx hc) (lowGeometry15W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (531458888316902459 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry15W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (225958839976830241 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry15W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (133 / 250) (601615411438310517 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry15W_hz2 hx hc) (lowGeometry15W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (133 / 250) (322808683879228053 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry15W_hz33 hx hc) (lowGeometry15W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (133 / 250) (322808683879228053 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry15W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry15W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (468541111683097541 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry15W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (219530773337232883 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry15W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (18686459426465263 / 40000000000000000) (213 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry15W_hz2 hx hc) (lowGeometry15W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (211579764670742993 / 500000000000000000) (213 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry15W_hz38 hx hc) (lowGeometry15W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (211579764670742993 / 500000000000000000) (213 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry15W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry15W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (187 / 400) (117 / 250) θ) :
    OverlapGuard n θ lowWideWindow (5923997 / 15625000) (145700713 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (56887983 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry15W_hz12 hx hc).2
  have hrp := (lowGeometry15W_hz16 hx hc).2
  have hbn := (lowGeometry15W_hz21 hx hc).2
  have hlo := (lowGeometry15W_hz40 hx hc).1
  have hhi := (lowGeometry15W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry15C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (187 / 400) (117 / 250) θ := hc

theorem lowGeometry15C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry15C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (133 / 250) (213 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry15C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (24871 / 100000) (24921 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry15C_hz0 hx hc) (lowGeometry15C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (24921 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry15C_hz3 hx hc) (lowGeometry15C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (2790665243270859 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry15C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (4018557950310037 / 125000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry15C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (187 / 200) (117 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry15C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry15C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry15C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (5849063925108017 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry15C_hz7 hx hc) (lowGeometry15C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (61393783228020381 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry15C_hz6 hx hc) (lowGeometry15C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (61393783228020381 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry15C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry15C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (146047 / 20000) (91377 / 12500) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry15C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (91377 / 100000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry15C_hz13 hx hc) (lowGeometry15C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (62307553228020381 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry15C_hz12 hx hc) (lowGeometry15C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (62307553228020381 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry15C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry15C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (117 / 2000000) (θ * x) := bmul (lowGeometry15C_hz0 hx hc) (lowGeometry15C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (54981203007519 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry15C_hz17 hx hc) (lowGeometry15C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (10486296105634153 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry15C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (30200532784226361 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry15C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (30200532784226361 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry15C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry15C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (61149 / 40000) (38259 / 25000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry15C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry15C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (4277486237558223 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry15C_hz22 hx hc) (lowGeometry15C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry15C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry15C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry15C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry15C_hz26 hx hc) (lowGeometry15C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry15C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 0 (17652642062117243 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry15C_hz24 hx hc) (lowGeometry15C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (1030200532784226361 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry15C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B 1 (530656568874451927 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry15C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (133 / 250) (565149245851291303 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry15C_hz2 hx hc) (lowGeometry15C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (133 / 250) (291400943956704273 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry15C_hz33 hx hc) (lowGeometry15C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (133 / 250) (291400943956704273 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry15C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry15C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (969799467215773639 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry15C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (940511006611998409 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry15C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (500351855517583153 / 1000000000000000000) (213 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry15C_hz2 hx hc) (lowGeometry15C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (48269921345546591 / 100000000000000000) (213 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry15C_hz38 hx hc) (lowGeometry15C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry15C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (187 / 400) (117 / 250) θ) : B (48269921345546591 / 100000000000000000) (213 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry15C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry15C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (187 / 400) (117 / 250) θ) :
    OverlapGuard n θ lowCoreWindow (454387443 / 1000000000) (620922681 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (7674223 / 125000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry15C_hz12 hx hc).2
  have hrp := (lowGeometry15C_hz16 hx hc).2
  have hbn := (lowGeometry15C_hz21 hx hc).2
  have hlo := (lowGeometry15C_hz40 hx hc).1
  have hhi := (lowGeometry15C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry16W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (117 / 250) (937 / 2000) θ := hc

theorem lowGeometry16W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry16W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (1063 / 2000) (133 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (124371 / 500000) (124621 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry16W_hz0 hx hc) (lowGeometry16W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (124621 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry16W_hz3 hx hc) (lowGeometry16W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (5581688812536937 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry16W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (16745066437610811 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry16W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (117 / 125) (937 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry16W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry16W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (937 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry16W_hz7 hx hc) (lowGeometry16W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (28457566437610811 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry16W_hz6 hx hc) (lowGeometry16W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (28457566437610811 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry16W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry16W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (468 / 25) (937 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry16W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (937 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry16W_hz13 hx hc) (lowGeometry16W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (29043191437610811 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry16W_hz12 hx hc) (lowGeometry16W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (29043191437610811 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry16W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry16W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (937 / 16000000) (θ * x) := bmul (lowGeometry16W_hz0 hx hc) (lowGeometry16W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (110183443085607 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry16W_hz17 hx hc) (lowGeometry16W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (2099366028929753 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry16W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (6298098086789259 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry16W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (6298098086789259 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry16W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry16W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (468 / 125) (937 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry16W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry16W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (41903913898346061 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry16W_hz22 hx hc) (lowGeometry16W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry16W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry16W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry16W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry16W_hz26 hx hc) (lowGeometry16W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry16W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (550612086965497 / 12500000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry16W_hz24 hx hc) (lowGeometry16W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (106298098086789259 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry16W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (1129928565686867033 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry16W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (1063 / 2000) (300560998472706631 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry16W_hz2 hx hc) (lowGeometry16W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (1063 / 2000) (322585481951326511 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry16W_hz33 hx hc) (lowGeometry16W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (1063 / 2000) (322585481951326511 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry16W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry16W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (93701901913210741 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry16W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (27437645069228021 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry16W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (466659467337430181 / 1000000000000000000) (133 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry16W_hz2 hx hc) (lowGeometry16W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (422610500380190421 / 1000000000000000000) (133 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry16W_hz38 hx hc) (lowGeometry16W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (422610500380190421 / 1000000000000000000) (133 / 250) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry16W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry16W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (117 / 250) (937 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (378624629 / 1000000000) (728044459 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (56915133 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry16W_hz12 hx hc).2
  have hrp := (lowGeometry16W_hz16 hx hc).2
  have hbn := (lowGeometry16W_hz21 hx hc).2
  have hlo := (lowGeometry16W_hz40 hx hc).1
  have hhi := (lowGeometry16W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry16C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (117 / 250) (937 / 2000) θ := hc

theorem lowGeometry16C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry16C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (1063 / 2000) (133 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (124371 / 500000) (124621 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry16C_hz0 hx hc) (lowGeometry16C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (124621 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry16C_hz3 hx hc) (lowGeometry16C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (5581688812536937 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry16C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (16075263780106379 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry16C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (117 / 125) (937 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry16C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry16C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (29276564625140021 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry16C_hz7 hx hc) (lowGeometry16C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (61427092185352779 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry16C_hz6 hx hc) (lowGeometry16C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (61427092185352779 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry16C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry16C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (91377 / 12500) (731797 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry16C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (731797 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry16C_hz13 hx hc) (lowGeometry16C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (62341838435352779 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry16C_hz12 hx hc) (lowGeometry16C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (62341838435352779 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry16C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry16C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (937 / 16000000) (θ * x) := bmul (lowGeometry16C_hz0 hx hc) (lowGeometry16C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (110183443085607 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry16C_hz17 hx hc) (lowGeometry16C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (2099366028929753 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry16C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (7557717704147111 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry16C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (7557717704147111 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry16C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry16C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (38259 / 25000) (306399 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry16C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry16C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (17128224805948953 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry16C_hz22 hx hc) (lowGeometry16C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry16C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry16C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry16C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry16C_hz26 hx hc) (lowGeometry16C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry16C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 0 (8835750861220009 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry16C_hz24 hx hc) (lowGeometry16C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (257557717704147111 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry16C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B 1 (1061375647183506147 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry16C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (1063 / 2000) (564651844301625271 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry16C_hz2 hx hc) (lowGeometry16C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (1063 / 2000) (582323346024065289 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry16C_hz33 hx hc) (lowGeometry16C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (1063 / 2000) (582323346024065289 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry16C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry16C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (242442282295852889 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry16C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (94045216391715237 / 100000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry16C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (124962581280491621 / 250000000000000000) (133 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry16C_hz2 hx hc) (lowGeometry16C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (241089411699763233 / 500000000000000000) (133 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry16C_hz38 hx hc) (lowGeometry16C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry16C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (117 / 250) (937 / 2000) θ) : B (241089411699763233 / 500000000000000000) (133 / 250) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry16C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry16C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (117 / 250) (937 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (453882927 / 1000000000) (77554357 / 125000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61427093 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry16C_hz12 hx hc).2
  have hrp := (lowGeometry16C_hz16 hx hc).2
  have hbn := (lowGeometry16C_hz21 hx hc).2
  have hlo := (lowGeometry16C_hz40 hx hc).1
  have hhi := (lowGeometry16C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry17W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (937 / 2000) (469 / 1000) θ := hc

theorem lowGeometry17W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry17W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (531 / 1000) (1063 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry17W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (497547 / 2000000) (498547 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry17W_hz0 hx hc) (lowGeometry17W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (498547 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry17W_hz3 hx hc) (lowGeometry17W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (697755189652861 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry17W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (2093265568958583 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry17W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (937 / 1000) (469 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry17W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry17W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry17W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (469 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry17W_hz7 hx hc) (lowGeometry17W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (3558890568958583 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry17W_hz6 hx hc) (lowGeometry17W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (3558890568958583 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry17W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry17W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (937 / 50) (469 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry17W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (469 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry17W_hz13 hx hc) (lowGeometry17W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (3632171818958583 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry17W_hz12 hx hc) (lowGeometry17W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (3632171818958583 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry17W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry17W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (469 / 8000000) (θ * x) := bmul (lowGeometry17W_hz0 hx hc) (lowGeometry17W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (55202448210923 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry17W_hz17 hx hc) (lowGeometry17W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (210147468623199 / 20000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry17W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (630442405869597 / 10000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry17W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (630442405869597 / 10000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry17W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry17W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (937 / 250) (469 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry17W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry17W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (41948635257896057 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry17W_hz22 hx hc) (lowGeometry17W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry17W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry17W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry17W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry17W_hz26 hx hc) (lowGeometry17W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry17W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (44095977594333933 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry17W_hz24 hx hc) (lowGeometry17W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (10630442405869597 / 10000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry17W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (1130063057445105857 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry17W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (531 / 1000) (600628515032073763 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry17W_hz2 hx hc) (lowGeometry17W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (531 / 1000) (40295280789150481 / 62500000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry17W_hz33 hx hc) (lowGeometry17W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (531 / 1000) (40295280789150481 / 62500000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry17W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry17W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (9369557594130403 / 10000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry17W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (54867880943579191 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry17W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (233078758248324403 / 500000000000000000) (1063 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry17W_hz2 hx hc) (lowGeometry17W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (422061538902314873 / 1000000000000000000) (1063 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry17W_hz38 hx hc) (lowGeometry17W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (422061538902314873 / 1000000000000000000) (1063 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry17W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry17W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (937 / 2000) (469 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (189056793 / 500000000) (181896291 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (113884499 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry17W_hz12 hx hc).2
  have hrp := (lowGeometry17W_hz16 hx hc).2
  have hbn := (lowGeometry17W_hz21 hx hc).2
  have hlo := (lowGeometry17W_hz40 hx hc).1
  have hhi := (lowGeometry17W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry17C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (937 / 2000) (469 / 1000) θ := hc

theorem lowGeometry17C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry17C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (531 / 1000) (1063 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry17C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (497547 / 2000000) (498547 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry17C_hz0 hx hc) (lowGeometry17C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (498547 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry17C_hz3 hx hc) (lowGeometry17C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (697755189652861 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry17C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (6430511827840767 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry17C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (937 / 1000) (469 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry17C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry17C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry17C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (29307809624739957 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry17C_hz7 hx hc) (lowGeometry17C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (3841273047746487 / 62500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry17C_hz6 hx hc) (lowGeometry17C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (3841273047746487 / 62500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry17C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry17C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (731797 / 100000) (366289 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry17C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (366289 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry17C_hz13 hx hc) (lowGeometry17C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (3898505703996487 / 62500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry17C_hz12 hx hc) (lowGeometry17C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (3898505703996487 / 62500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry17C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry17C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (469 / 8000000) (θ * x) := bmul (lowGeometry17C_hz0 hx hc) (lowGeometry17C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (55202448210923 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry17C_hz17 hx hc) (lowGeometry17C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (210147468623199 / 20000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry17C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (1891327217608791 / 62500000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry17C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (1891327217608791 / 62500000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry17C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry17C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (306399 / 200000) (153363 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry17C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry17C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (8573252330832507 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry17C_hz22 hx hc) (lowGeometry17C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry17C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry17C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry17C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry17C_hz26 hx hc) (lowGeometry17C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry17C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 0 (17690361382762793 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry17C_hz24 hx hc) (lowGeometry17C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (64391327217608791 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry17C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B 1 (66339888333522667 / 62500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry17C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (531 / 1000) (564154410388276761 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry17C_hz2 hx hc) (lowGeometry17C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (531 / 1000) (290922385885519777 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry17C_hz33 hx hc) (lowGeometry17C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (531 / 1000) (290922385885519777 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry17C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry17C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (60608672782391209 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry17C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (940393271409400047 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry17C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (3901162711862433 / 7812500000000000) (1063 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry17C_hz2 hx hc) (lowGeometry17C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (481658465735628631 / 1000000000000000000) (1063 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry17C_hz38 hx hc) (lowGeometry17C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry17C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (937 / 2000) (469 / 1000) θ) : B (481658465735628631 / 1000000000000000000) (1063 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry17C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry17C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (937 / 2000) (469 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (453378487 / 1000000000) (30997347 / 50000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61460369 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry17C_hz12 hx hc).2
  have hrp := (lowGeometry17C_hz16 hx hc).2
  have hbn := (lowGeometry17C_hz21 hx hc).2
  have hlo := (lowGeometry17C_hz40 hx hc).1
  have hhi := (lowGeometry17C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry18W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (469 / 1000) (939 / 2000) θ := hc

theorem lowGeometry18W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry18W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (1061 / 2000) (531 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (497609 / 2000000) (498609 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry18W_hz0 hx hc) (lowGeometry18W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (498609 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry18W_hz3 hx hc) (lowGeometry18W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (2791194300832531 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry18W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (8373582902497593 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry18W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (469 / 500) (939 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry18W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry18W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (939 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry18W_hz7 hx hc) (lowGeometry18W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (14242332902497593 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry18W_hz6 hx hc) (lowGeometry18W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (14242332902497593 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry18W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry18W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (469 / 25) (939 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry18W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (939 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry18W_hz13 hx hc) (lowGeometry18W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (14535770402497593 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry18W_hz12 hx hc) (lowGeometry18W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (14535770402497593 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry18W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry18W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (939 / 16000000) (θ * x) := bmul (lowGeometry18W_hz0 hx hc) (lowGeometry18W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (22125353440151 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry18W_hz17 hx hc) (lowGeometry18W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (10517925993310421 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry18W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (31553777979931263 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry18W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (31553777979931263 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry18W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry18W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (469 / 125) (939 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry18W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry18W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (41993356617446053 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry18W_hz22 hx hc) (lowGeometry18W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry18W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry18W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry18W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry18W_hz26 hx hc) (lowGeometry18W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry18W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (22071494115714053 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry18W_hz24 hx hc) (lowGeometry18W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (531553777979931263 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry18W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (1130197675538952233 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry18W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (1061 / 2000) (150033741427795909 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry18W_hz2 hx hc) (lowGeometry18W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (1061 / 2000) (322138976971305871 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry18W_hz33 hx hc) (lowGeometry18W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (1061 / 2000) (322138976971305871 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry18W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry18W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (468446222020068737 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry18W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (54860465731218883 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry18W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (232827816563292939 / 500000000000000000) (531 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry18W_hz2 hx hc) (lowGeometry18W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (105378161223789443 / 250000000000000000) (531 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry18W_hz38 hx hc) (lowGeometry18W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (105378161223789443 / 250000000000000000) (531 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry18W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry18W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (469 / 1000) (939 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (188801339 / 500000000) (727125683 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (14242333 / 125000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry18W_hz12 hx hc).2
  have hrp := (lowGeometry18W_hz16 hx hc).2
  have hbn := (lowGeometry18W_hz21 hx hc).2
  have hlo := (lowGeometry18W_hz40 hx hc).1
  have hhi := (lowGeometry18W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry18C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (469 / 1000) (939 / 2000) θ := hc

theorem lowGeometry18C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry18C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (1061 / 2000) (531 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (497609 / 2000000) (498609 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry18C_hz0 hx hc) (lowGeometry18C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (498609 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry18C_hz3 hx hc) (lowGeometry18C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (2791194300832531 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry18C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (16077279172795379 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry18C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (469 / 500) (939 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry18C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry18C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (29339054624339893 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry18C_hz7 hx hc) (lowGeometry18C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (61493612969930651 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry18C_hz6 hx hc) (lowGeometry18C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (61493612969930651 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry18C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry18C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (366289 / 50000) (733359 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry18C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (733359 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry18C_hz13 hx hc) (lowGeometry18C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (62410311719930651 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry18C_hz12 hx hc) (lowGeometry18C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (62410311719930651 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry18C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry18C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (939 / 16000000) (θ * x) := bmul (lowGeometry18C_hz0 hx hc) (lowGeometry18C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (22125353440151 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry18C_hz17 hx hc) (lowGeometry18C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (10517925993310421 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry18C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (30291626860734013 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry18C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (30291626860734013 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry18C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry18C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (153363 / 100000) (307053 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry18C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry18C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (8582392258690537 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry18C_hz22 hx hc) (lowGeometry18C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry18C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry18C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry18C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry18C_hz26 hx hc) (lowGeometry18C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry18C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 0 (17709221043085567 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry18C_hz24 hx hc) (lowGeometry18C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (1030291626860734013 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry18C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B 1 (1061500836379337969 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry18C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (1061 / 2000) (281828472058714231 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry18C_hz2 hx hc) (lowGeometry18C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (1061 / 2000) (581366165160514029 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry18C_hz33 hx hc) (lowGeometry18C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (1061 / 2000) (581366165160514029 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry18C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry18C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (969708373139265987 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry18C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (235083582234100479 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry18C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (3897245011724697 / 7812500000000000) (531 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry18C_hz2 hx hc) (lowGeometry18C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (481138140457675649 / 1000000000000000000) (531 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry18C_hz38 hx hc) (lowGeometry18C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry18C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (469 / 1000) (939 / 2000) θ) : B (481138140457675649 / 1000000000000000000) (531 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry18C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry18C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (469 / 1000) (939 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (3622993 / 8000000) (309729467 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61493613 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry18C_hz12 hx hc).2
  have hrp := (lowGeometry18C_hz16 hx hc).2
  have hbn := (lowGeometry18C_hz21 hx hc).2
  have hlo := (lowGeometry18C_hz40 hx hc).1
  have hhi := (lowGeometry18C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry19W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (939 / 2000) (47 / 100) θ := hc

theorem lowGeometry19W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry19W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (53 / 100) (1061 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry19W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (49767 / 200000) (49867 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry19W_hz0 hx hc) (lowGeometry19W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (49867 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry19W_hz3 hx hc) (lowGeometry19W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1395682516727927 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry19W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (4187047550183781 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry19W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (939 / 1000) (47 / 50) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry19W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry19W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry19W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (47 / 1000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry19W_hz7 hx hc) (lowGeometry19W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (7124547550183781 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry19W_hz6 hx hc) (lowGeometry19W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (7124547550183781 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry19W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry19W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (939 / 50) (94 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry19W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (47 / 20000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry19W_hz13 hx hc) (lowGeometry19W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (7271422550183781 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry19W_hz12 hx hc) (lowGeometry19W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (7271422550183781 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry19W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry19W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (47 / 800000) (θ * x) := bmul (lowGeometry19W_hz0 hx hc) (lowGeometry19W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (55424528301887 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry19W_hz17 hx hc) (lowGeometry19W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1316060982414557 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry19W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (3948182947243671 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry19W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (3948182947243671 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry19W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry19W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (939 / 250) (94 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry19W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry19W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (42038077976996049 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry19W_hz22 hx hc) (lowGeometry19W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry19W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry19W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry19W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry19W_hz26 hx hc) (lowGeometry19W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry19W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (44189998868522279 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry19W_hz24 hx hc) (lowGeometry19W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (66448182947243671 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry19W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (1130332420349533337 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry19W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (53 / 100) (149910337248856859 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry19W_hz2 hx hc) (lowGeometry19W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (53 / 100) (128766269572789943 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry19W_hz33 hx hc) (lowGeometry19W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (53 / 100) (128766269572789943 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry19W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry19W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (58551817052756329 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry19W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (109706088965742299 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry19W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (465153817214747347 / 1000000000000000000) (1061 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry19W_hz2 hx hc) (lowGeometry19W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (105240954586556267 / 250000000000000000) (1061 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry19W_hz38 hx hc) (lowGeometry19W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (105240954586556267 / 250000000000000000) (1061 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry19W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry19W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (939 / 2000) (47 / 100) θ) :
    OverlapGuard n θ lowWideWindow (75418381 / 200000000) (726666013 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (113992761 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry19W_hz12 hx hc).2
  have hrp := (lowGeometry19W_hz16 hx hc).2
  have hbn := (lowGeometry19W_hz21 hx hc).2
  have hlo := (lowGeometry19W_hz40 hx hc).1
  have hhi := (lowGeometry19W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry19C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (939 / 2000) (47 / 100) θ := hc

theorem lowGeometry19C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry19C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (53 / 100) (1061 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry19C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (49767 / 200000) (49867 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry19C_hz0 hx hc) (lowGeometry19C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (49867 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry19C_hz3 hx hc) (lowGeometry19C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1395682516727927 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry19C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (32156525185411439 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry19C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (939 / 1000) (47 / 50) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry19C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry19C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry19C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (29370299623939829 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry19C_hz7 hx hc) (lowGeometry19C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (15381706202337817 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry19C_hz6 hx hc) (lowGeometry19C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (15381706202337817 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry19C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry19C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (733359 / 100000) (36707 / 5000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry19C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (36707 / 40000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry19C_hz13 hx hc) (lowGeometry19C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (15611124952337817 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry19C_hz12 hx hc) (lowGeometry19C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (15611124952337817 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry19C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry19C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (47 / 800000) (θ * x) := bmul (lowGeometry19C_hz0 hx hc) (lowGeometry19C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (55424528301887 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry19C_hz17 hx hc) (lowGeometry19C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (1316060982414557 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry19C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (15161022517415697 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry19C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (15161022517415697 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry19C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry19C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (307053 / 200000) (15369 / 10000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry19C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry19C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (3436612874619427 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry19C_hz22 hx hc) (lowGeometry19C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry19C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry19C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry19C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry19C_hz26 hx hc) (lowGeometry19C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry19C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 0 (8864040351704171 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry19C_hz24 hx hc) (lowGeometry19C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (515161022517415697 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry19C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B 1 (265390879121189283 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry19C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (53 / 100) (563159445495163659 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry19C_hz2 hx hc) (lowGeometry19C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (53 / 100) (580887526198572001 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry19C_hz33 hx hc) (lowGeometry19C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (53 / 100) (580887526198572001 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry19C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry19C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (484838977482584303 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry19C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (188055067269086311 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry19C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (124586482065769681 / 250000000000000000) (1061 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry19C_hz2 hx hc) (lowGeometry19C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (240308923779835191 / 500000000000000000) (1061 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry19C_hz38 hx hc) (lowGeometry19C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry19C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (939 / 2000) (47 / 100) θ) : B (240308923779835191 / 500000000000000000) (1061 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry19C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry19C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (939 / 2000) (47 / 100) θ) :
    OverlapGuard n θ lowCoreWindow (452369839 / 1000000000) (618970837 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (2461073 / 40000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry19C_hz12 hx hc).2
  have hrp := (lowGeometry19C_hz16 hx hc).2
  have hbn := (lowGeometry19C_hz21 hx hc).2
  have hlo := (lowGeometry19C_hz40 hx hc).1
  have hhi := (lowGeometry19C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry20W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (47 / 100) (941 / 2000) θ := hc

theorem lowGeometry20W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry20W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (1059 / 2000) (53 / 100) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (49773 / 200000) (49873 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry20W_hz0 hx hc) (lowGeometry20W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (49873 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry20W_hz3 hx hc) (lowGeometry20W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (1395766478498463 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry20W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (4187299435495389 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry20W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (47 / 50) (941 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry20W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry20W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (941 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry20W_hz7 hx hc) (lowGeometry20W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (7127924435495389 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry20W_hz6 hx hc) (lowGeometry20W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (7127924435495389 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry20W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry20W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (94 / 5) (941 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry20W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (941 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry20W_hz13 hx hc) (lowGeometry20W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (7274955685495389 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry20W_hz12 hx hc) (lowGeometry20W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (7274955685495389 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry20W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry20W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (941 / 16000000) (θ * x) := bmul (lowGeometry20W_hz0 hx hc) (lowGeometry20W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (111071765816809 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry20W_hz17 hx hc) (lowGeometry20W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (10539059057468509 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry20W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (31617177172405527 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry20W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (31617177172405527 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry20W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry20W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (94 / 25) (941 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry20W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry20W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (8416559867309209 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry20W_hz22 hx hc) (lowGeometry20W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry20W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry20W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry20W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry20W_hz26 hx hc) (lowGeometry20W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry20W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (11059252376404113 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry20W_hz24 hx hc) (lowGeometry20W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (531617177172405527 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry20W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (1130467292259027233 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry20W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (1059 / 2000) (299573832448642217 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry20W_hz2 hx hc) (lowGeometry20W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (1059 / 2000) (321692337201450443 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry20W_hz33 hx hc) (lowGeometry20W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (1059 / 2000) (321692337201450443 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry20W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry20W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (468382822827594473 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry20W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (109691234359972877 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry20W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (232326034374422553 / 500000000000000000) (53 / 100) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry20W_hz2 hx hc) (lowGeometry20W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (210207529621614327 / 500000000000000000) (53 / 100) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry20W_hz38 hx hc) (lowGeometry20W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (210207529621614327 / 500000000000000000) (53 / 100) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry20W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry20W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (47 / 100) (941 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (188290633 / 500000000) (726206157 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (114046791 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry20W_hz12 hx hc).2
  have hrp := (lowGeometry20W_hz16 hx hc).2
  have hbn := (lowGeometry20W_hz21 hx hc).2
  have hlo := (lowGeometry20W_hz40 hx hc).1
  have hhi := (lowGeometry20W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry20C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (47 / 100) (941 / 2000) θ := hc

theorem lowGeometry20C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry20C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (1059 / 2000) (53 / 100) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (49773 / 200000) (49873 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry20C_hz0 hx hc) (lowGeometry20C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (49873 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry20C_hz3 hx hc) (lowGeometry20C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (1395766478498463 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry20C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (8039614916151147 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry20C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (47 / 50) (941 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry20C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry20C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (5880308924707953 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry20C_hz7 hx hc) (lowGeometry20C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (61560004288144353 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry20C_hz6 hx hc) (lowGeometry20C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (61560004288144353 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry20C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry20C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (36707 / 5000) (734921 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry20C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (734921 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry20C_hz13 hx hc) (lowGeometry20C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (62478655538144353 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry20C_hz12 hx hc) (lowGeometry20C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (62478655538144353 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry20C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry20C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (941 / 16000000) (θ * x) := bmul (lowGeometry20C_hz0 hx hc) (lowGeometry20C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (111071765816809 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry20C_hz17 hx hc) (lowGeometry20C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (10539059057468509 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry20C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (15176245042754653 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry20C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (15176245042754653 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry20C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry20C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (15369 / 10000) (307707 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry20C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry20C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (4300336057203299 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry20C_hz22 hx hc) (lowGeometry20C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry20C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry20C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry20C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry20C_hz26 hx hc) (lowGeometry20C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry20C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 0 (17746940363731117 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry20C_hz24 hx hc) (lowGeometry20C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (515176245042754653 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry20C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B 1 (1061626253825409553 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry20C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (1059 / 2000) (70332739315933383 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry20C_hz2 hx hc) (lowGeometry20C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (1059 / 2000) (580408854891198181 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry20C_hz33 hx hc) (lowGeometry20C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (1059 / 2000) (580408854891198181 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry20C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry20C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (484823754957245347 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry20C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (117527036685421541 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry20C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (497844527399445647 / 1000000000000000000) (53 / 100) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry20C_hz2 hx hc) (lowGeometry20C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (48009758703571453 / 100000000000000000) (53 / 100) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry20C_hz38 hx hc) (lowGeometry20C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry20C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (941 / 2000) θ) : B (48009758703571453 / 100000000000000000) (53 / 100) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry20C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry20C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (47 / 100) (941 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (451865629 / 1000000000) (12369653 / 20000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12312001 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry20C_hz12 hx hc).2
  have hrp := (lowGeometry20C_hz16 hx hc).2
  have hbn := (lowGeometry20C_hz21 hx hc).2
  have hlo := (lowGeometry20C_hz40 hx hc).1
  have hhi := (lowGeometry20C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry21W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (941 / 2000) (471 / 1000) θ := hc

theorem lowGeometry21W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry21W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (529 / 1000) (1059 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry21W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (497789 / 2000000) (498789 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry21W_hz0 hx hc) (lowGeometry21W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (498789 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry21W_hz3 hx hc) (lowGeometry21W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (5583396143925309 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry21W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (16750188431775927 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry21W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (941 / 1000) (471 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry21W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry21W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry21W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (471 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry21W_hz7 hx hc) (lowGeometry21W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (28525188431775927 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry21W_hz6 hx hc) (lowGeometry21W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (28525188431775927 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry21W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry21W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (941 / 50) (471 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry21W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (471 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry21W_hz13 hx hc) (lowGeometry21W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (29113938431775927 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry21W_hz12 hx hc) (lowGeometry21W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (29113938431775927 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry21W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry21W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (471 / 8000000) (θ * x) := bmul (lowGeometry21W_hz0 hx hc) (lowGeometry21W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (55647448015123 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry21W_hz17 hx hc) (lowGeometry21W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (2109927923226251 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry21W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (6329783769678753 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry21W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (6329783769678753 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry21W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry21W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (941 / 250) (471 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry21W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry21W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (1053188017402401 / 25000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry21W_hz22 hx hc) (lowGeometry21W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry21W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry21W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry21W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry21W_hz26 hx hc) (lowGeometry21W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry21W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (1383875629459707 / 31250000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry21W_hz24 hx hc) (lowGeometry21W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (106329783769678753 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry21W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (1130602291650663917 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry21W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (529 / 1000) (119730782685805309 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry21W_hz2 hx hc) (lowGeometry21W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (529 / 1000) (642937933571737169 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry21W_hz33 hx hc) (lowGeometry21W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (529 / 1000) (642937933571737169 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry21W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry21W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (93670216230321247 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry21W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (219352735215878449 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry21W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (232075193858399399 / 500000000000000000) (1059 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry21W_hz2 hx hc) (lowGeometry21W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (209933183787044087 / 500000000000000000) (1059 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry21W_hz38 hx hc) (lowGeometry21W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (209933183787044087 / 500000000000000000) (1059 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry21W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry21W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (941 / 2000) (471 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (376070763 / 1000000000) (11339783 / 15625000) ∧ radiusMinus n θ lowWideWindow ≤ (57050377 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry21W_hz12 hx hc).2
  have hrp := (lowGeometry21W_hz16 hx hc).2
  have hbn := (lowGeometry21W_hz21 hx hc).2
  have hlo := (lowGeometry21W_hz40 hx hc).1
  have hhi := (lowGeometry21W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry21C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (941 / 2000) (471 / 1000) θ := hc

theorem lowGeometry21C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry21C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (529 / 1000) (1059 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry21C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (497789 / 2000000) (498789 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry21C_hz0 hx hc) (lowGeometry21C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (498789 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry21C_hz3 hx hc) (lowGeometry21C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (5583396143925309 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry21C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (1608018089450489 / 50000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry21C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (941 / 1000) (471 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry21C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry21C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry21C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (29432789623139701 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry21C_hz7 hx hc) (lowGeometry21C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (61593151412149481 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry21C_hz6 hx hc) (lowGeometry21C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (61593151412149481 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry21C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry21C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (734921 / 100000) (367851 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry21C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (367851 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry21C_hz13 hx hc) (lowGeometry21C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (62512778912149481 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry21C_hz12 hx hc) (lowGeometry21C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (62512778912149481 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry21C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry21C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (471 / 8000000) (θ * x) := bmul (lowGeometry21C_hz0 hx hc) (lowGeometry21C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (55647448015123 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry21C_hz17 hx hc) (lowGeometry21C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (2109927923226251 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry21C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (6076592418891603 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry21C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (6076592418891603 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry21C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry21C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (307707 / 200000) (154017 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry21C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry21C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (17219624084529257 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry21C_hz22 hx hc) (lowGeometry21C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry21C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry21C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry21C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry21C_hz26 hx hc) (lowGeometry21C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry21C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 0 (4441450006013473 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry21C_hz24 hx hc) (lowGeometry21C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (206076592418891603 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry21C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B 1 (1061689048574549303 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry21C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (529 / 1000) (35135271951263991 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry21C_hz2 hx hc) (lowGeometry21C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (529 / 1000) (144982537811069437 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry21C_hz33 hx hc) (lowGeometry21C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (529 / 1000) (144982537811069437 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry21C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry21C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (193923407581108397 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry21C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (470078600098358621 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry21C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (497343158904063421 / 1000000000000000000) (1059 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry21C_hz2 hx hc) (lowGeometry21C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (479577358880009529 / 1000000000000000000) (1059 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry21C_hz38 hx hc) (lowGeometry21C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry21C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (941 / 2000) (471 / 1000) θ) : B (479577358880009529 / 1000000000000000000) (1059 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry21C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry21C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (941 / 2000) (471 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (451361497 / 1000000000) (617994373 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (962393 / 15625000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry21C_hz12 hx hc).2
  have hrp := (lowGeometry21C_hz16 hx hc).2
  have hbn := (lowGeometry21C_hz21 hx hc).2
  have hlo := (lowGeometry21C_hz40 hx hc).1
  have hhi := (lowGeometry21C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry22W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (471 / 1000) (943 / 2000) θ := hc

theorem lowGeometry22W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry22W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (1057 / 2000) (529 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry22W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (497847 / 2000000) (498847 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry22W_hz0 hx hc) (lowGeometry22W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (498847 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry22W_hz3 hx hc) (lowGeometry22W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (5583720757702699 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry22W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (16751162273108097 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry22W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (471 / 500) (943 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry22W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry22W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry22W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (943 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry22W_hz7 hx hc) (lowGeometry22W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (28538662273108097 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry22W_hz6 hx hc) (lowGeometry22W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (28538662273108097 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry22W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry22W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (471 / 25) (943 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry22W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (943 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry22W_hz13 hx hc) (lowGeometry22W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (29128037273108097 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry22W_hz12 hx hc) (lowGeometry22W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (29128037273108097 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry22W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry22W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (943 / 16000000) (θ * x) := bmul (lowGeometry22W_hz0 hx hc) (lowGeometry22W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (111518448438979 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry22W_hz17 hx hc) (lowGeometry22W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (5280114781872147 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry22W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (15840344345616441 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry22W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (15840344345616441 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry22W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry22W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (471 / 125) (943 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry22W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry22W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (10543060513911509 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry22W_hz22 hx hc) (lowGeometry22W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry22W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry22W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry22W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry22W_hz26 hx hc) (lowGeometry22W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry22W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (11082757694951199 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry22W_hz24 hx hc) (lowGeometry22W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (265840344345616441 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry22W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (1130737418908734773 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry22W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (1057 / 2000) (119632018920544139 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry22W_hz2 hx hc) (lowGeometry22W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (1057 / 2000) (642491125382525491 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry22W_hz33 hx hc) (lowGeometry22W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (1057 / 2000) (642491125382525491 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry22W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry22W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (234159655654383559 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry22W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (219322977344717929 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry22W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (463648774106733701 / 1000000000000000000) (529 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry22W_hz2 hx hc) (lowGeometry22W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (83863548665385781 / 200000000000000000) (529 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry22W_hz38 hx hc) (lowGeometry22W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (83863548665385781 / 200000000000000000) (529 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry22W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry22W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (471 / 1000) (943 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (187780197 / 500000000) (725285881 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (2283093 / 20000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry22W_hz12 hx hc).2
  have hrp := (lowGeometry22W_hz16 hx hc).2
  have hbn := (lowGeometry22W_hz21 hx hc).2
  have hlo := (lowGeometry22W_hz40 hx hc).1
  have hhi := (lowGeometry22W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry22C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (471 / 1000) (943 / 2000) θ := hc

theorem lowGeometry22C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry22C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (1057 / 2000) (529 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry22C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (497847 / 2000000) (498847 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry22C_hz0 hx hc) (lowGeometry22C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (498847 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry22C_hz3 hx hc) (lowGeometry22C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (5583720757702699 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry22C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (32162231564367547 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry22C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (471 / 500) (943 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry22C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry22C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry22C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (29464034622739637 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry22C_hz7 hx hc) (lowGeometry22C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (3851641636694199 / 62500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry22C_hz6 hx hc) (lowGeometry22C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (3851641636694199 / 62500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry22C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry22C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (367851 / 50000) (736483 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry22C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (736483 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry22C_hz13 hx hc) (lowGeometry22C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (3909179371069199 / 62500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry22C_hz12 hx hc) (lowGeometry22C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (3909179371069199 / 62500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry22C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry22C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (943 / 16000000) (θ * x) := bmul (lowGeometry22C_hz0 hx hc) (lowGeometry22C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (111518448438979 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry22C_hz17 hx hc) (lowGeometry22C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (5280114781872147 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry22C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (30413461143583567 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry22C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (30413461143583567 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry22C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry22C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (154017 / 100000) (308361 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry22C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry22C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (8618951970122659 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry22C_hz22 hx hc) (lowGeometry22C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry22C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry22C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry22C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry22C_hz26 hx hc) (lowGeometry22C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry22C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 0 (17784659684376667 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry22C_hz24 hx hc) (lowGeometry22C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (1030413461143583567 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry22C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B 1 (530875950452949701 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry22C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (1057 / 2000) (35104172223701299 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry22C_hz2 hx hc) (lowGeometry22C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (1057 / 2000) (579451415263597451 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry22C_hz33 hx hc) (lowGeometry22C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (1057 / 2000) (579451415263597451 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry22C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry22C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (969586538856416433 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry22C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (940098056331565133 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry22C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (124210455692808043 / 250000000000000000) (529 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry22C_hz2 hx hc) (lowGeometry22C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (95811432617371101 / 200000000000000000) (529 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry22C_hz38 hx hc) (lowGeometry22C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry22C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (471 / 1000) (943 / 2000) θ) : B (95811432617371101 / 200000000000000000) (529 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry22C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry22C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (471 / 1000) (943 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (450857441 / 1000000000) (123501201 / 200000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61626267 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry22C_hz12 hx hc).2
  have hrp := (lowGeometry22C_hz16 hx hc).2
  have hbn := (lowGeometry22C_hz21 hx hc).2
  have hlo := (lowGeometry22C_hz40 hx hc).1
  have hhi := (lowGeometry22C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry23W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (943 / 2000) (59 / 125) θ := hc

theorem lowGeometry23W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry23W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (66 / 125) (1057 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry23W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (31119 / 125000) (62363 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry23W_hz0 hx hc) (lowGeometry23W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (62363 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry23W_hz3 hx hc) (lowGeometry23W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (2792019878152733 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry23W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (8376059634458199 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry23W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (943 / 1000) (118 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry23W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry23W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry23W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (59 / 1250) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry23W_hz7 hx hc) (lowGeometry23W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (14276059634458199 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry23W_hz6 hx hc) (lowGeometry23W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (14276059634458199 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry23W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry23W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (943 / 50) (472 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry23W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (59 / 25000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry23W_hz13 hx hc) (lowGeometry23W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (14571059634458199 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry23W_hz12 hx hc) (lowGeometry23W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (14571059634458199 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry23W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry23W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (59 / 1000000) (θ * x) := bmul (lowGeometry23W_hz0 hx hc) (lowGeometry23W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (4469696969697 / 40000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry23W_hz17 hx hc) (lowGeometry23W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (5285414464411117 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry23W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (15856243393233351 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry23W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (15856243393233351 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry23W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry23W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (943 / 250) (472 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry23W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry23W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (329820026681219 / 7812500000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry23W_hz22 hx hc) (lowGeometry23W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry23W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry23W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry23W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry23W_hz26 hx hc) (lowGeometry23W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry23W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (44378041416898969 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry23W_hz24 hx hc) (lowGeometry23W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (265856243393233351 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry23W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (1130872674418594109 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry23W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (66 / 125) (597666208430226987 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry23W_hz2 hx hc) (lowGeometry23W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (66 / 125) (160511062461781489 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry23W_hz33 hx hc) (lowGeometry23W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (66 / 125) (160511062461781489 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry23W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry23W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (234143756606766649 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry23W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (219293195031715123 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry23W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (463147227906982339 / 1000000000000000000) (1057 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry23W_hz2 hx hc) (lowGeometry23W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (41876918649008337 / 100000000000000000) (1057 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry23W_hz38 hx hc) (lowGeometry23W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (41876918649008337 / 100000000000000000) (1057 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry23W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry23W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (943 / 2000) (59 / 125) θ) :
    OverlapGuard n θ lowWideWindow (4688127 / 12500000) (724825463 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (57104239 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry23W_hz12 hx hc).2
  have hrp := (lowGeometry23W_hz16 hx hc).2
  have hbn := (lowGeometry23W_hz21 hx hc).2
  have hlo := (lowGeometry23W_hz40 hx hc).1
  have hhi := (lowGeometry23W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry23C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (943 / 2000) (59 / 125) θ := hc

theorem lowGeometry23C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry23C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (66 / 125) (1057 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry23C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (31119 / 125000) (62363 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry23C_hz0 hx hc) (lowGeometry23C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (62363 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry23C_hz3 hx hc) (lowGeometry23C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (2792019878152733 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry23C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (6432813799263897 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry23C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (943 / 1000) (118 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry23C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry23C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry23C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (29495279622339573 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry23C_hz7 hx hc) (lowGeometry23C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (30829674309329529 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry23C_hz6 hx hc) (lowGeometry23C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (30829674309329529 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry23C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry23C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (736483 / 100000) (46079 / 6250) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry23C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (46079 / 50000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry23C_hz13 hx hc) (lowGeometry23C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (31290464309329529 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry23C_hz12 hx hc) (lowGeometry23C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (31290464309329529 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry23C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry23C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (59 / 1000000) (θ * x) := bmul (lowGeometry23C_hz0 hx hc) (lowGeometry23C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (4469696969697 / 40000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry23C_hz17 hx hc) (lowGeometry23C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (5285414464411117 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry23C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (15221993657504017 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry23C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (15221993657504017 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry23C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry23C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (308361 / 200000) (19293 / 12500) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry23C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry23C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (8628091897980689 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry23C_hz22 hx hc) (lowGeometry23C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry23C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry23C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry23C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry23C_hz26 hx hc) (lowGeometry23C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry23C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 0 (17803519344699441 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry23C_hz24 hx hc) (lowGeometry23C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (515221993657504017 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry23C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B 1 (1061814810993652439 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry23C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (66 / 125) (112233825522029063 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry23C_hz2 hx hc) (lowGeometry23C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (66 / 125) (144743161738711189 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry23C_hz33 hx hc) (lowGeometry23C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (66 / 125) (144743161738711189 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry23C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry23C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (484778006342495983 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry23C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (470019430866810151 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry23C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (496340518995351519 / 1000000000000000000) (1057 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry23C_hz2 hx hc) (lowGeometry23C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (239268499825326039 / 500000000000000000) (1057 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry23C_hz38 hx hc) (lowGeometry23C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry23C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (943 / 2000) (59 / 125) θ) : B (239268499825326039 / 500000000000000000) (1057 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry23C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry23C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (943 / 2000) (59 / 125) θ) :
    OverlapGuard n θ lowCoreWindow (450353461 / 1000000000) (617017547 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61659349 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry23C_hz12 hx hc).2
  have hrp := (lowGeometry23C_hz16 hx hc).2
  have hbn := (lowGeometry23C_hz21 hx hc).2
  have hlo := (lowGeometry23C_hz40 hx hc).1
  have hhi := (lowGeometry23C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry24W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (59 / 125) (189 / 400) θ := hc

theorem lowGeometry24W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry24W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (211 / 400) (66 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry24W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (12449 / 50000) (6237 / 25000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry24W_hz0 hx hc) (lowGeometry24W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (6237 / 200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry24W_hz3 hx hc) (lowGeometry24W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (2792176570347943 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry24W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (8376529711043829 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry24W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (118 / 125) (189 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry24W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry24W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry24W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (189 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry24W_hz7 hx hc) (lowGeometry24W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (14282779711043829 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry24W_hz6 hx hc) (lowGeometry24W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (14282779711043829 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry24W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry24W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (472 / 25) (189 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry24W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (189 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry24W_hz13 hx hc) (lowGeometry24W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (14578092211043829 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry24W_hz12 hx hc) (lowGeometry24W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (14578092211043829 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry24W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry24W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (189 / 3200000) (θ * x) := bmul (lowGeometry24W_hz0 hx hc) (lowGeometry24W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (2239336492891 / 20000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry24W_hz17 hx hc) (lowGeometry24W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (2116287547991057 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry24W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (6348862643973171 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry24W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (6348862643973171 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry24W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry24W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (472 / 125) (189 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry24W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry24W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (10565421193686507 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry24W_hz22 hx hc) (lowGeometry24W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry24W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry24W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry24W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry24W_hz26 hx hc) (lowGeometry24W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry24W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (22212526026996571 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry24W_hz24 hx hc) (lowGeometry24W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (106348862643973171 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry24W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (1131008058566667221 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry24W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (211 / 400) (597172254923200293 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry24W_hz2 hx hc) (lowGeometry24W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (211 / 400) (128319461395438687 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry24W_hz33 hx hc) (lowGeometry24W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (211 / 400) (128319461395438687 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry24W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry24W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (93651137356026829 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry24W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (43852677640387019 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry24W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (9252914982121661 / 20000000000000000) (66 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry24W_hz2 hx hc) (lowGeometry24W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (104555174263022477 / 250000000000000000) (66 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry24W_hz38 hx hc) (lowGeometry24W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (104555174263022477 / 250000000000000000) (66 / 125) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry24W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry24W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (59 / 125) (189 / 400) θ) :
    OverlapGuard n θ lowWideWindow (18727003 / 50000000) (724364857 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (57131119 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry24W_hz12 hx hc).2
  have hrp := (lowGeometry24W_hz16 hx hc).2
  have hbn := (lowGeometry24W_hz21 hx hc).2
  have hlo := (lowGeometry24W_hz40 hx hc).1
  have hhi := (lowGeometry24W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry24C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (59 / 125) (189 / 400) θ := hc

theorem lowGeometry24C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry24C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (211 / 400) (66 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry24C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (12449 / 50000) (6237 / 25000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry24C_hz0 hx hc) (lowGeometry24C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (6237 / 200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry24C_hz3 hx hc) (lowGeometry24C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (2792176570347943 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry24C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (2010367130650519 / 62500000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry24C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (118 / 125) (189 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry24C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry24C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry24C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (29526524621939509 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry24C_hz7 hx hc) (lowGeometry24C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (61692398712347813 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry24C_hz6 hx hc) (lowGeometry24C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (61692398712347813 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry24C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry24C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (46079 / 6250) (147609 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry24C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (147609 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry24C_hz13 hx hc) (lowGeometry24C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (62614954962347813 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry24C_hz12 hx hc) (lowGeometry24C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (62614954962347813 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry24C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry24C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (189 / 3200000) (θ * x) := bmul (lowGeometry24C_hz0 hx hc) (lowGeometry24C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (2239336492891 / 20000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry24C_hz17 hx hc) (lowGeometry24C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (2116287547991057 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry24C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (30474540691071221 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry24C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (30474540691071221 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry24C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry24C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (19293 / 12500) (61803 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry24C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry24C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (17274463651677439 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry24C_hz22 hx hc) (lowGeometry24C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry24C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry24C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry24C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry24C_hz26 hx hc) (lowGeometry24C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry24C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 0 (2227797375627777 / 125000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry24C_hz24 hx hc) (lowGeometry24C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (1030474540691071221 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry24C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B 1 (530938889506237099 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry24C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (211 / 400) (560671467318586377 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry24C_hz2 hx hc) (lowGeometry24C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (211 / 400) (578493846323608593 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry24C_hz33 hx hc) (lowGeometry24C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (211 / 400) (578493846323608593 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry24C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry24C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (969525459308928779 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry24C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (939979616248189313 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry24C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (247919623785459931 / 500000000000000000) (66 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry24C_hz2 hx hc) (lowGeometry24C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (239008434282948823 / 500000000000000000) (66 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry24C_hz38 hx hc) (lowGeometry24C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry24C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 125) (189 / 400) θ) : B (239008434282948823 / 500000000000000000) (66 / 125) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry24C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry24C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (59 / 125) (189 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (224924779 / 500000000) (616529 / 1000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61692399 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry24C_hz12 hx hc).2
  have hrp := (lowGeometry24C_hz16 hx hc).2
  have hbn := (lowGeometry24C_hz21 hx hc).2
  have hlo := (lowGeometry24C_hz40 hx hc).1
  have hhi := (lowGeometry24C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry25W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (189 / 400) (473 / 1000) θ := hc

theorem lowGeometry25W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry25W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (527 / 1000) (211 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry25W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (99603 / 400000) (99803 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry25W_hz0 hx hc) (lowGeometry25W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (99803 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry25W_hz3 hx hc) (lowGeometry25W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (349041306988693 / 62500000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry25W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1047123920966079 / 15625000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry25W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (189 / 200) (473 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry25W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry25W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry25W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (473 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry25W_hz7 hx hc) (lowGeometry25W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1786186420966079 / 15625000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry25W_hz6 hx hc) (lowGeometry25W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1786186420966079 / 15625000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry25W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry25W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (189 / 10) (473 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry25W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (473 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry25W_hz13 hx hc) (lowGeometry25W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1823139545966079 / 15625000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry25W_hz12 hx hc) (lowGeometry25W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1823139545966079 / 15625000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry25W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry25W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (473 / 8000000) (θ * x) := bmul (lowGeometry25W_hz0 hx hc) (lowGeometry25W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (11219165085389 / 100000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry25W_hz17 hx hc) (lowGeometry25W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (5296028012904813 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry25W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (15888084038714439 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry25W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (15888084038714439 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry25W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry25W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (189 / 50) (473 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry25W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry25W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (5288300766787003 / 125000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry25W_hz22 hx hc) (lowGeometry25W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry25W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry25W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry25W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry25W_hz26 hx hc) (lowGeometry25W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry25W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (8894412538217463 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry25W_hz24 hx hc) (lowGeometry25W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (265888084038714439 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry25W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (1131143571740455553 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry25W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (527 / 1000) (119335646818618061 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry25W_hz2 hx hc) (lowGeometry25W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (527 / 1000) (32057514839208881 / 50000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry25W_hz33 hx hc) (lowGeometry25W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (527 / 1000) (32057514839208881 / 50000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry25W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry25W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (234111915961285561 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry25W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (54808389195064033 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry25W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (231072168846389963 / 500000000000000000) (211 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry25W_hz2 hx hc) (lowGeometry25W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (417672275001692611 / 1000000000000000000) (211 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry25W_hz38 hx hc) (lowGeometry25W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (417672275001692611 / 1000000000000000000) (211 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry25W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry25W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (189 / 400) (473 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (74806019 / 200000000) (11311001 / 15625000) ∧ radiusMinus n θ lowWideWindow ≤ (114315931 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry25W_hz12 hx hc).2
  have hrp := (lowGeometry25W_hz16 hx hc).2
  have hbn := (lowGeometry25W_hz21 hx hc).2
  have hlo := (lowGeometry25W_hz40 hx hc).1
  have hhi := (lowGeometry25W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry25C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (189 / 400) (473 / 1000) θ := hc

theorem lowGeometry25C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry25C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (527 / 1000) (211 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry25C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (99603 / 400000) (99803 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry25C_hz0 hx hc) (lowGeometry25C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (99803 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry25C_hz3 hx hc) (lowGeometry25C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (349041306988693 / 62500000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry25C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (32167646852077947 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry25C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (189 / 200) (473 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry25C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry25C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry25C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (5911553924307889 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry25C_hz7 hx hc) (lowGeometry25C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (3857838529601087 / 62500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry25C_hz6 hx hc) (lowGeometry25C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (3857838529601087 / 62500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry25C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry25C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (147609 / 20000) (369413 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry25C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (369413 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry25C_hz13 hx hc) (lowGeometry25C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (3915559310851087 / 62500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry25C_hz12 hx hc) (lowGeometry25C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (3915559310851087 / 62500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry25C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry25C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (473 / 8000000) (θ * x) := bmul (lowGeometry25C_hz0 hx hc) (lowGeometry25C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (11219165085389 / 100000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry25C_hz17 hx hc) (lowGeometry25C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (5296028012904813 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry25C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (30505121354331723 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry25C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (30505121354331723 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry25C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry25C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (61803 / 40000) (154671 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry25C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry25C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (34585487014787 / 2000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry25C_hz22 hx hc) (lowGeometry25C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry25C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry25C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry25C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry25C_hz26 hx hc) (lowGeometry25C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry25C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 0 (557538708292031 / 31250000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry25C_hz24 hx hc) (lowGeometry25C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (1030505121354331723 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry25C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B 1 (33185650160547061 / 31250000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry25C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (527 / 1000) (56017377471003439 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry25C_hz2 hx hc) (lowGeometry25C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (527 / 1000) (289007506687689691 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry25C_hz33 hx hc) (lowGeometry25C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (527 / 1000) (289007506687689691 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry25C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry25C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (969494878645668277 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry25C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (939920319720179059 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry25C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (123834502123133591 / 250000000000000000) (211 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry25C_hz2 hx hc) (lowGeometry25C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (119374192456797343 / 250000000000000000) (211 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry25C_hz38 hx hc) (lowGeometry25C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry25C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (189 / 400) (473 / 1000) θ) : B (119374192456797343 / 250000000000000000) (211 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry25C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry25C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (189 / 400) (473 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (449345731 / 1000000000) (308020181 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61725417 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry25C_hz12 hx hc).2
  have hrp := (lowGeometry25C_hz16 hx hc).2
  have hbn := (lowGeometry25C_hz21 hx hc).2
  have hlo := (lowGeometry25C_hz40 hx hc).1
  have hhi := (lowGeometry25C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry26W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (473 / 1000) (947 / 2000) θ := hc

theorem lowGeometry26W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry26W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (1053 / 2000) (527 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry26W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (498069 / 2000000) (499069 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry26W_hz0 hx hc) (lowGeometry26W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (499069 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry26W_hz3 hx hc) (lowGeometry26W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (698120383825383 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry26W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (2094361151476149 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry26W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (473 / 500) (947 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry26W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry26W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry26W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (947 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry26W_hz7 hx hc) (lowGeometry26W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (3574048651476149 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry26W_hz6 hx hc) (lowGeometry26W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (3574048651476149 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry26W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry26W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (473 / 25) (947 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry26W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (947 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry26W_hz13 hx hc) (lowGeometry26W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (3648033026476149 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry26W_hz12 hx hc) (lowGeometry26W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (3648033026476149 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry26W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry26W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (947 / 16000000) (θ * x) := bmul (lowGeometry26W_hz0 hx hc) (lowGeometry26W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (112416904083571 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry26W_hz17 hx hc) (lowGeometry26W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (5301341907563853 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry26W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (15904025722691559 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry26W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (15904025722691559 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry26W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry26W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (473 / 125) (947 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry26W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry26W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (42351127493846019 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry26W_hz22 hx hc) (lowGeometry26W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry26W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry26W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry26W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry26W_hz26 hx hc) (lowGeometry26W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry26W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (44519073328181487 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry26W_hz24 hx hc) (lowGeometry26W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (265904025722691559 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry26W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (1131279214328541029 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry26W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (1053 / 2000) (596184145951141123 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry26W_hz2 hx hc) (lowGeometry26W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (1053 / 2000) (64070321927932261 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry26W_hz33 hx hc) (lowGeometry26W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (1053 / 2000) (64070321927932261 / 100000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry26W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry26W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (234095974277308441 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry26W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (219203700691369021 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry26W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (230821496828011579 / 500000000000000000) (527 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry26W_hz2 hx hc) (lowGeometry26W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (417123920327841671 / 1000000000000000000) (527 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry26W_hz38 hx hc) (lowGeometry26W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (417123920327841671 / 1000000000000000000) (527 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry26W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry26W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (473 / 1000) (947 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (46690033 / 125000000) (144688617 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (114369557 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry26W_hz12 hx hc).2
  have hrp := (lowGeometry26W_hz16 hx hc).2
  have hbn := (lowGeometry26W_hz21 hx hc).2
  have hlo := (lowGeometry26W_hz40 hx hc).1
  have hhi := (lowGeometry26W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry26C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (473 / 1000) (947 / 2000) θ := hc

theorem lowGeometry26C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry26C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (1053 / 2000) (527 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry26C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (498069 / 2000000) (499069 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry26C_hz0 hx hc) (lowGeometry26C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (499069 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry26C_hz3 hx hc) (lowGeometry26C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (698120383825383 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry26C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (32169387286673649 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry26C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (473 / 500) (947 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry26C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry26C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry26C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (29589014621139381 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry26C_hz7 hx hc) (lowGeometry26C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (6175840190781303 / 100000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry26C_hz6 hx hc) (lowGeometry26C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (6175840190781303 / 100000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry26C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry26C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (369413 / 50000) (739607 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry26C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (739607 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry26C_hz13 hx hc) (lowGeometry26C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (6268291065781303 / 100000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry26C_hz12 hx hc) (lowGeometry26C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (6268291065781303 / 100000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry26C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry26C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (947 / 16000000) (θ * x) := bmul (lowGeometry26C_hz0 hx hc) (lowGeometry26C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (112416904083571 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry26C_hz17 hx hc) (lowGeometry26C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (5301341907563853 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry26C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (15267864693783897 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry26C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (15267864693783897 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry26C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry26C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (154671 / 100000) (309669 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry26C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry26C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (17311023363109561 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry26C_hz22 hx hc) (lowGeometry26C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry26C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry26C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry26C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry26C_hz26 hx hc) (lowGeometry26C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry26C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 0 (17860098325667767 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry26C_hz24 hx hc) (lowGeometry26C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (515267864693783897 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry26C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B 1 (26550097238609159 / 25000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry26C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (1053 / 2000) (34979753111867567 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry26C_hz2 hx hc) (lowGeometry26C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (1053 / 2000) (577536148115548839 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry26C_hz33 hx hc) (lowGeometry26C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (1053 / 2000) (577536148115548839 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry26C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry26C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (484732135306216103 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry26C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (939860971994095183 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry26C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (494836801754891113 / 1000000000000000000) (527 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry26C_hz2 hx hc) (lowGeometry26C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (238488351714611673 / 500000000000000000) (527 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry26C_hz38 hx hc) (lowGeometry26C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry26C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (473 / 1000) (947 / 2000) θ) : B (238488351714611673 / 500000000000000000) (527 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry26C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry26C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (473 / 1000) (947 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (448841981 / 1000000000) (307775817 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (30879201 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry26C_hz12 hx hc).2
  have hrp := (lowGeometry26C_hz16 hx hc).2
  have hbn := (lowGeometry26C_hz21 hx hc).2
  have hlo := (lowGeometry26C_hz40 hx hc).1
  have hhi := (lowGeometry26C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry27W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (947 / 2000) (237 / 500) θ := hc

theorem lowGeometry27W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry27W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (263 / 500) (1053 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry27W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (249061 / 1000000) (249561 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry27W_hz0 hx hc) (lowGeometry27W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (249561 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry27W_hz3 hx hc) (lowGeometry27W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (2792629808979343 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry27W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (8377889426938029 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry27W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (947 / 1000) (237 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry27W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry27W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry27W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (237 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry27W_hz7 hx hc) (lowGeometry27W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (14302889426938029 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry27W_hz6 hx hc) (lowGeometry27W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (14302889426938029 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry27W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry27W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (947 / 50) (474 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry27W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (237 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry27W_hz13 hx hc) (lowGeometry27W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (14599139426938029 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry27W_hz12 hx hc) (lowGeometry27W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (14599139426938029 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry27W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry27W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (237 / 4000000) (θ * x) := bmul (lowGeometry27W_hz0 hx hc) (lowGeometry27W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (112642585551331 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry27W_hz17 hx hc) (lowGeometry27W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (2122664227345729 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry27W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (6367992682037187 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry27W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (6367992682037187 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry27W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry27W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (947 / 250) (474 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry27W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry27W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (8479169770679203 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry27W_hz22 hx hc) (lowGeometry27W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry27W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry27W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry27W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry27W_hz26 hx hc) (lowGeometry27W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry27W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (2228304198263783 / 50000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry27W_hz24 hx hc) (lowGeometry27W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (106367992682037187 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry27W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (1131414986720591657 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry27W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (263 / 500) (148922497627097877 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry27W_hz2 hx hc) (lowGeometry27W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (263 / 500) (20008002327302099 / 31250000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry27W_hz33 hx hc) (lowGeometry27W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (263 / 500) (20008002327302099 / 31250000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry27W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry27W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (93632007317962813 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry27W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (54793454964944011 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry27W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (115285429246242199 / 250000000000000000) (1053 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry27W_hz2 hx hc) (lowGeometry27W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (26035977063730821 / 62500000000000000) (1053 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry27W_hz38 hx hc) (lowGeometry27W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (26035977063730821 / 62500000000000000) (1053 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry27W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry27W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (947 / 2000) (237 / 500) θ) :
    OverlapGuard n θ lowWideWindow (186505283 / 500000000) (361490959 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (28605779 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry27W_hz12 hx hc).2
  have hrp := (lowGeometry27W_hz16 hx hc).2
  have hbn := (lowGeometry27W_hz21 hx hc).2
  have hlo := (lowGeometry27W_hz40 hx hc).1
  have hhi := (lowGeometry27W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry27C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (947 / 2000) (237 / 500) θ := hc

theorem lowGeometry27C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry27C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (263 / 500) (1053 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry27C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (249061 / 1000000) (249561 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry27C_hz0 hx hc) (lowGeometry27C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (249561 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry27C_hz3 hx hc) (lowGeometry27C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (2792629808979343 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry27C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (2010693462465127 / 62500000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry27C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (947 / 1000) (237 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry27C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry27C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry27C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (29620259620739317 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry27C_hz7 hx hc) (lowGeometry27C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (61791355020181349 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry27C_hz6 hx hc) (lowGeometry27C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (61791355020181349 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry27C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry27C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (739607 / 100000) (185097 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry27C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (185097 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry27C_hz13 hx hc) (lowGeometry27C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (62716840020181349 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry27C_hz12 hx hc) (lowGeometry27C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (62716840020181349 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry27C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry27C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (237 / 4000000) (θ * x) := bmul (lowGeometry27C_hz0 hx hc) (lowGeometry27C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (112642585551331 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry27C_hz17 hx hc) (lowGeometry27C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (2122664227345729 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry27C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (15283182436889249 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry27C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (15283182436889249 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry27C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry27C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (309669 / 200000) (77499 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry27C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry27C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (17329303218825621 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry27C_hz22 hx hc) (lowGeometry27C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry27C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry27C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry27C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry27C_hz26 hx hc) (lowGeometry27C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry27C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 0 (17878957985990541 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry27C_hz24 hx hc) (lowGeometry27C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (515283182436889249 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry27C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B 1 (1062067032409153957 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry27C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (263 / 500) (559178292563419559 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry27C_hz2 hx hc) (lowGeometry27C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (263 / 500) (5770572505494101 / 10000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry27C_hz33 hx hc) (lowGeometry27C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (263 / 500) (5770572505494101 / 10000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry27C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry27C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (484716817563110751 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry27C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (234950393228509991 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry27C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (494335627352785021 / 1000000000000000000) (1053 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry27C_hz2 hx hc) (lowGeometry27C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (5955708367084931 / 12500000000000000) (1053 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry27C_hz38 hx hc) (lowGeometry27C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry27C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (947 / 2000) (237 / 500) θ) : B (5955708367084931 / 12500000000000000) (1053 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry27C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry27C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (947 / 2000) (237 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (448338307 / 1000000000) (19220713 / 31250000) ∧ radiusMinus n θ lowCoreWindow ≤ (15447839 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry27C_hz12 hx hc).2
  have hrp := (lowGeometry27C_hz16 hx hc).2
  have hbn := (lowGeometry27C_hz21 hx hc).2
  have hlo := (lowGeometry27C_hz40 hx hc).1
  have hhi := (lowGeometry27C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry28W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (237 / 500) (949 / 2000) θ := hc

theorem lowGeometry28W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry28W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (1051 / 2000) (263 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry28W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (249087 / 1000000) (249587 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry28W_hz0 hx hc) (lowGeometry28W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (249587 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry28W_hz3 hx hc) (lowGeometry28W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (5585550554779717 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry28W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (16756651664339151 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry28W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (237 / 250) (949 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry28W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry28W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry28W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (949 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry28W_hz7 hx hc) (lowGeometry28W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (28619151664339151 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry28W_hz6 hx hc) (lowGeometry28W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (28619151664339151 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry28W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry28W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (474 / 25) (949 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry28W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (949 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry28W_hz13 hx hc) (lowGeometry28W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (29212276664339151 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry28W_hz12 hx hc) (lowGeometry28W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (29212276664339151 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry28W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry28W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (949 / 16000000) (θ * x) := bmul (lowGeometry28W_hz0 hx hc) (lowGeometry28W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (14108587059943 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry28W_hz17 hx hc) (lowGeometry28W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (10623968019508719 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry28W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (31871904058526157 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry28W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (31871904058526157 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry28W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry28W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (474 / 125) (949 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry28W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry28W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (42440570212946011 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry28W_hz22 hx hc) (lowGeometry28W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry28W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry28W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry28W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry28W_hz26 hx hc) (lowGeometry28W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry28W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (44613094602369833 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry28W_hz24 hx hc) (lowGeometry28W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (531871904058526157 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry28W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (1131550889307368213 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry28W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (1051 / 2000) (595195767775675681 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry28W_hz2 hx hc) (lowGeometry28W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (1051 / 2000) (319904431189022757 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry28W_hz33 hx hc) (lowGeometry28W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (1051 / 2000) (319904431189022757 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry28W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry28W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (468128095941473843 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry28W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (219143914209789739 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry28W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (460640507668978031 / 1000000000000000000) (263 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry28W_hz2 hx hc) (lowGeometry28W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (208013706533304099 / 500000000000000000) (263 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry28W_hz38 hx hc) (lowGeometry28W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (208013706533304099 / 500000000000000000) (263 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry28W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry28W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (237 / 500) (949 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (372501003 / 1000000000) (144504113 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (114476607 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry28W_hz12 hx hc).2
  have hrp := (lowGeometry28W_hz16 hx hc).2
  have hbn := (lowGeometry28W_hz21 hx hc).2
  have hlo := (lowGeometry28W_hz40 hx hc).1
  have hhi := (lowGeometry28W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry28C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (237 / 500) (949 / 2000) θ := hc

theorem lowGeometry28C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry28C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (1051 / 2000) (263 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry28C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (249087 / 1000000) (249587 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry28C_hz0 hx hc) (lowGeometry28C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (249587 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry28C_hz3 hx hc) (lowGeometry28C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (5585550554779717 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry28C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (3217277119553117 / 100000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry28C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (237 / 250) (949 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry28C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry28C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry28C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (29651504620339253 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry28C_hz7 hx hc) (lowGeometry28C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (61824275815870423 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry28C_hz6 hx hc) (lowGeometry28C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (61824275815870423 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry28C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry28C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (185097 / 25000) (741169 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry28C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (741169 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry28C_hz13 hx hc) (lowGeometry28C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (62750737065870423 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry28C_hz12 hx hc) (lowGeometry28C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (62750737065870423 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry28C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry28C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (949 / 16000000) (θ * x) := bmul (lowGeometry28C_hz0 hx hc) (lowGeometry28C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (14108587059943 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry28C_hz17 hx hc) (lowGeometry28C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (10623968019508719 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry28C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (30597027896185111 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry28C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (30597027896185111 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry28C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry28C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (77499 / 50000) (310323 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry28C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry28C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (8673791537270841 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry28C_hz22 hx hc) (lowGeometry28C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry28C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry28C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry28C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry28C_hz26 hx hc) (lowGeometry28C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry28C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 0 (4474454411578329 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry28C_hz24 hx hc) (lowGeometry28C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (1030597027896185111 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry28C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B 1 (132766279238556269 / 125000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry28C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (1051 / 2000) (27934025151792239 / 50000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry28C_hz2 hx hc) (lowGeometry28C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (1051 / 2000) (36036145042634881 / 62500000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry28C_hz33 hx hc) (lowGeometry28C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (1051 / 2000) (36036145042634881 / 62500000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry28C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry28C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (969402972103814889 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry28C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (939742122323709707 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry28C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (493834485281109451 / 1000000000000000000) (263 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry28C_hz2 hx hc) (lowGeometry28C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (95187333526959227 / 200000000000000000) (263 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry28C_hz38 hx hc) (lowGeometry28C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry28C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (237 / 500) (949 / 2000) θ) : B (95187333526959227 / 200000000000000000) (263 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry28C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry28C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (237 / 500) (949 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (447834709 / 1000000000) (153643477 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15456069 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry28C_hz12 hx hc).2
  have hrp := (lowGeometry28C_hz16 hx hc).2
  have hbn := (lowGeometry28C_hz21 hx hc).2
  have hlo := (lowGeometry28C_hz40 hx hc).1
  have hhi := (lowGeometry28C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry29W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (949 / 2000) (19 / 40) θ := hc

theorem lowGeometry29W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry29W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (21 / 40) (1051 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry29W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (19929 / 80000) (19969 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry29W_hz0 hx hc) (lowGeometry29W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (19969 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry29W_hz3 hx hc) (lowGeometry29W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (1396458970485707 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry29W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (4189376911457121 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry29W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (949 / 1000) (19 / 20) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry29W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry29W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry29W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (19 / 400) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry29W_hz7 hx hc) (lowGeometry29W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (7158126911457121 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry29W_hz6 hx hc) (lowGeometry29W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (7158126911457121 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry29W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry29W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (949 / 50) 19 (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry29W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (19 / 8000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry29W_hz13 hx hc) (lowGeometry29W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (7306564411457121 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry29W_hz12 hx hc) (lowGeometry29W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (7306564411457121 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry29W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry29W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (19 / 320000) (θ * x) := bmul (lowGeometry29W_hz0 hx hc) (lowGeometry29W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (113095238095239 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry29W_hz17 hx hc) (lowGeometry29W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (2658656123110403 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry29W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (7975968369331209 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry29W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (7975968369331209 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry29W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry29W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (949 / 250) (19 / 5) (θ * (8 : ℝ)) := bmul (lowGeometry29W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry29W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (42485291572496007 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry29W_hz22 hx hc) (lowGeometry29W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry29W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry29W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry29W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry29W_hz26 hx hc) (lowGeometry29W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry29W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (8932021047892801 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry29W_hz24 hx hc) (lowGeometry29W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (132975968369331209 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry29W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (1131686922480727949 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry29W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (21 / 40) (297350738881811269 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry29W_hz2 hx hc) (lowGeometry29W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (21 / 40) (639361583003086543 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry29W_hz33 hx hc) (lowGeometry29W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (21 / 40) (639361583003086543 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry29W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry29W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (117024031630668791 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry29W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (43822796733106463 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry29W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (460139365697617861 / 1000000000000000000) (1051 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry29W_hz2 hx hc) (lowGeometry29W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (3245931722329327 / 7812500000000000) (1051 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry29W_hz38 hx hc) (lowGeometry29W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (3245931722329327 / 7812500000000000) (1051 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry29W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry29W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (949 / 2000) (19 / 40) θ) :
    OverlapGuard n θ lowWideWindow (185995787 / 500000000) (361029513 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (114530031 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry29W_hz12 hx hc).2
  have hrp := (lowGeometry29W_hz16 hx hc).2
  have hbn := (lowGeometry29W_hz21 hx hc).2
  have hlo := (lowGeometry29W_hz40 hx hc).1
  have hhi := (lowGeometry29W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry29C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (949 / 2000) (19 / 40) θ := hc

theorem lowGeometry29C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry29C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (21 / 40) (1051 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry29C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (19929 / 80000) (19969 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry29C_hz0 hx hc) (lowGeometry29C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (19969 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry29C_hz3 hx hc) (lowGeometry29C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (1396458970485707 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry29C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (3217441467999069 / 100000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry29C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (949 / 1000) (19 / 20) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry29C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry29C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry29C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (29682749619939189 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry29C_hz7 hx hc) (lowGeometry29C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (61857164299929879 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry29C_hz6 hx hc) (lowGeometry29C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (61857164299929879 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry29C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry29C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (741169 / 100000) (14839 / 2000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry29C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (14839 / 16000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry29C_hz13 hx hc) (lowGeometry29C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (62784601799929879 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry29C_hz12 hx hc) (lowGeometry29C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (62784601799929879 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry29C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry29C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (19 / 320000) (θ * x) := bmul (lowGeometry29C_hz0 hx hc) (lowGeometry29C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (113095238095239 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry29C_hz17 hx hc) (lowGeometry29C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (2658656123110403 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry29C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (30627718538231843 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry29C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (30627718538231843 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry29C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry29C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (310323 / 200000) (6213 / 4000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry29C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry29C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (17365862930257743 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry29C_hz22 hx hc) (lowGeometry29C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry29C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry29C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry29C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry29C_hz26 hx hc) (lowGeometry29C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry29C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 0 (17916677306636091 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry29C_hz24 hx hc) (lowGeometry29C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (1030627718538231843 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry29C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B 1 (1062193494219320837 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry29C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (21 / 40) (5581826812122531 / 10000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry29C_hz2 hx hc) (lowGeometry29C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (21 / 40) (576099358518889191 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry29C_hz33 hx hc) (lowGeometry29C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (21 / 40) (576099358518889191 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry29C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry29C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (969372281461768157 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry29C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (117460327508299183 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry29C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (61666671941857071 / 125000000000000000) (1051 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry29C_hz2 hx hc) (lowGeometry29C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (475416698228220477 / 1000000000000000000) (1051 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry29C_hz38 hx hc) (lowGeometry29C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry29C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (949 / 2000) (19 / 40) θ) : B (475416698228220477 / 1000000000000000000) (1051 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry29C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry29C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (949 / 2000) (19 / 40) θ) :
    OverlapGuard n θ lowCoreWindow (447331187 / 1000000000) (61408491 / 100000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12371433 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry29C_hz12 hx hc).2
  have hrp := (lowGeometry29C_hz16 hx hc).2
  have hbn := (lowGeometry29C_hz21 hx hc).2
  have hlo := (lowGeometry29C_hz40 hx hc).1
  have hhi := (lowGeometry29C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry30W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (19 / 40) (951 / 2000) θ := hc

theorem lowGeometry30W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry30W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (1049 / 2000) (21 / 40) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry30W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (19931 / 80000) (19971 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry30W_hz0 hx hc) (lowGeometry30W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (19971 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry30W_hz3 hx hc) (lowGeometry30W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (2793057800153803 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry30W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (8379173400461409 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry30W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (19 / 20) (951 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry30W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry30W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry30W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (951 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry30W_hz7 hx hc) (lowGeometry30W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (14322923400461409 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry30W_hz6 hx hc) (lowGeometry30W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (14322923400461409 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry30W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry30W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 19 (951 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry30W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (951 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry30W_hz13 hx hc) (lowGeometry30W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (14620110900461409 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry30W_hz12 hx hc) (lowGeometry30W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (14620110900461409 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry30W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry30W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (951 / 16000000) (θ * x) := bmul (lowGeometry30W_hz0 hx hc) (lowGeometry30W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (28330552907531 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry30W_hz17 hx hc) (lowGeometry30W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (2661322646144723 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry30W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (7983967938434169 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry30W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (7983967938434169 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry30W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry30W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (19 / 5) (951 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry30W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry30W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (21265006466023001 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry30W_hz22 hx hc) (lowGeometry30W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry30W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry30W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry30W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry30W_hz26 hx hc) (lowGeometry30W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry30W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (44707115876558177 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry30W_hz24 hx hc) (lowGeometry30W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (132983967938434169 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry30W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (1131823086633631169 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry30W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (1049 / 2000) (148551780120664091 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry30W_hz2 hx hc) (lowGeometry30W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (1049 / 2000) (638914236359214541 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry30W_hz33 hx hc) (lowGeometry30W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (1049 / 2000) (638914236359214541 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry30W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry30W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (117016032061565831 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry30W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (5477100703773361 / 6250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry30W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (91927658212132091 / 200000000000000000) (21 / 40) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry30W_hz2 hx hc) (lowGeometry30W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (207465587592051139 / 500000000000000000) (21 / 40) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry30W_hz38 hx hc) (lowGeometry30W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (207465587592051139 / 500000000000000000) (21 / 40) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry30W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry30W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (19 / 40) (951 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (185741139 / 500000000) (7215973 / 10000000) ∧ radiusMinus n θ lowWideWindow ≤ (28645847 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry30W_hz12 hx hc).2
  have hrp := (lowGeometry30W_hz16 hx hc).2
  have hbn := (lowGeometry30W_hz21 hx hc).2
  have hlo := (lowGeometry30W_hz40 hx hc).1
  have hhi := (lowGeometry30W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry30C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (19 / 40) (951 / 2000) θ := hc

theorem lowGeometry30C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry30C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (1049 / 2000) (21 / 40) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry30C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (19931 / 80000) (19971 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry30C_hz0 hx hc) (lowGeometry30C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (19971 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry30C_hz3 hx hc) (lowGeometry30C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (2793057800153803 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry30C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (32176025857771811 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry30C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (19 / 20) (951 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry30C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry30C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry30C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (237711956956313 / 8000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry30C_hz7 hx hc) (lowGeometry30C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (7736252559663867 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry30C_hz6 hx hc) (lowGeometry30C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (7736252559663867 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry30C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry30C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (14839 / 2000) (742731 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry30C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (742731 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry30C_hz13 hx hc) (lowGeometry30C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (7852304278413867 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry30C_hz12 hx hc) (lowGeometry30C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (7852304278413867 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry30C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry30C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (951 / 16000000) (θ * x) := bmul (lowGeometry30C_hz0 hx hc) (lowGeometry30C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (28330552907531 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry30C_hz17 hx hc) (lowGeometry30C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (2661322646144723 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry30C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (30658436883587209 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry30C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (30658436883587209 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry30C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry30C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (6213 / 4000) (310977 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry30C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry30C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (4346035696493451 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry30C_hz22 hx hc) (lowGeometry30C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry30C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry30C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry30C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry30C_hz26 hx hc) (lowGeometry30C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry30C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 0 (8967768483479433 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry30C_hz24 hx hc) (lowGeometry30C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (1030658436883587209 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry30C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B 1 (1062256813519319319 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry30C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (1049 / 2000) (557684827097642643 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry30C_hz2 hx hc) (lowGeometry30C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (1049 / 2000) (575620364064601509 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry30C_hz33 hx hc) (lowGeometry30C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (1049 / 2000) (575620364064601509 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry30C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry30C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (969341563116412791 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry30C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (469811532992485241 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry30C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (492832298109117017 / 1000000000000000000) (21 / 40) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry30C_hz2 hx hc) (lowGeometry30C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (474896761142158151 / 1000000000000000000) (21 / 40) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry30C_hz38 hx hc) (lowGeometry30C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry30C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (19 / 40) (951 / 2000) θ) : B (474896761142158151 / 1000000000000000000) (21 / 40) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry30C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry30C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (19 / 40) (951 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (223413871 / 500000000) (613595823 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (61890021 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry30C_hz12 hx hc).2
  have hrp := (lowGeometry30C_hz16 hx hc).2
  have hbn := (lowGeometry30C_hz21 hx hc).2
  have hlo := (lowGeometry30C_hz40 hx hc).1
  have hhi := (lowGeometry30C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry31W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (951 / 2000) (119 / 250) θ := hc

theorem lowGeometry31W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry31W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (131 / 250) (1049 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry31W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (124581 / 500000) (124831 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry31W_hz0 hx hc) (lowGeometry31W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (124831 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry31W_hz3 hx hc) (lowGeometry31W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (2793194855358287 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry31W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (8379584566074861 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry31W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (951 / 1000) (119 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry31W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry31W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry31W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (119 / 2500) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry31W_hz7 hx hc) (lowGeometry31W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (14329584566074861 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry31W_hz6 hx hc) (lowGeometry31W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (14329584566074861 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry31W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry31W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (951 / 50) (476 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry31W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (119 / 50000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry31W_hz13 hx hc) (lowGeometry31W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (14627084566074861 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry31W_hz12 hx hc) (lowGeometry31W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (14627084566074861 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry31W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry31W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (119 / 2000000) (θ * x) := bmul (lowGeometry31W_hz0 hx hc) (lowGeometry31W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (113549618320611 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry31W_hz17 hx hc) (lowGeometry31W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (2131193265010107 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry31W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (6393579795030321 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry31W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (6393579795030321 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry31W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry31W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (951 / 250) (476 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry31W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry31W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (21287367145797999 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry31W_hz22 hx hc) (lowGeometry31W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry31W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry31W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry31W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry31W_hz26 hx hc) (lowGeometry31W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry31W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (895082530273047 / 20000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry31W_hz24 hx hc) (lowGeometry31W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (106393579795030321 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry31W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (1131959382160148417 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry31W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (131 / 250) (118742539188599569 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry31W_hz2 hx hc) (lowGeometry31W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (131 / 250) (127693364491330039 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry31W_hz33 hx hc) (lowGeometry31W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (131 / 250) (127693364491330039 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry31W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry31W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (93606420204969679 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry31W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (109527023794866947 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry31W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (459137283748082241 / 1000000000000000000) (1049 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry31W_hz2 hx hc) (lowGeometry31W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (414383157234429891 / 1000000000000000000) (1049 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry31W_hz38 hx hc) (lowGeometry31W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (414383157234429891 / 1000000000000000000) (1049 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry31W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry31W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (951 / 2000) (119 / 250) θ) :
    OverlapGuard n θ lowWideWindow (92743279 / 250000000) (721135387 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (114636677 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry31W_hz12 hx hc).2
  have hrp := (lowGeometry31W_hz16 hx hc).2
  have hbn := (lowGeometry31W_hz21 hx hc).2
  have hlo := (lowGeometry31W_hz40 hx hc).1
  have hhi := (lowGeometry31W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry31C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (951 / 2000) (119 / 250) θ := hc

theorem lowGeometry31C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry31C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (131 / 250) (1049 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry31C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (124581 / 500000) (124831 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry31C_hz0 hx hc) (lowGeometry31C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (124831 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry31C_hz3 hx hc) (lowGeometry31C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (2793194855358287 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry31C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (32177604733727467 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry31C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (951 / 1000) (119 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry31C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry31C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry31C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (29745239619139061 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry31C_hz7 hx hc) (lowGeometry31C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1935088886027079 / 31250000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry31C_hz6 hx hc) (lowGeometry31C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1935088886027079 / 31250000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry31C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry31C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (742731 / 100000) (92939 / 12500) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry31C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (92939 / 100000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry31C_hz13 hx hc) (lowGeometry31C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1964132323527079 / 31250000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry31C_hz12 hx hc) (lowGeometry31C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (1964132323527079 / 31250000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry31C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry31C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (119 / 2000000) (θ * x) := bmul (lowGeometry31C_hz0 hx hc) (lowGeometry31C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (113549618320611 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry31C_hz17 hx hc) (lowGeometry31C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (2131193265010107 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry31C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (30689183016145541 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry31C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (30689183016145541 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry31C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry31C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (310977 / 200000) (38913 / 25000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry31C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry31C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (3480484528337973 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry31C_hz22 hx hc) (lowGeometry31C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry31C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry31C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry31C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry31C_hz26 hx hc) (lowGeometry31C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry31C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 0 (17954396627281641 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry31C_hz24 hx hc) (lowGeometry31C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (1030689183016145541 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry31C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B 1 (531160095993244779 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry31C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (131 / 250) (278593470348456887 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry31C_hz2 hx hc) (lowGeometry31C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (131 / 250) (115028267464839083 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry31C_hz33 hx hc) (lowGeometry31C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (131 / 250) (115028267464839083 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry31C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry31C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (969310816983854459 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry31C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (939563459921907393 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry31C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (492331252999079473 / 1000000000000000000) (1049 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry31C_hz2 hx hc) (lowGeometry31C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (59297107046474729 / 125000000000000000) (1049 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry31C_hz38 hx hc) (lowGeometry31C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry31C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (951 / 2000) (119 / 250) θ) : B (59297107046474729 / 125000000000000000) (1049 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry31C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry31C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (951 / 2000) (119 / 250) θ) :
    OverlapGuard n θ lowCoreWindow (111581093 / 250000000) (122621329 / 200000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12384569 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry31C_hz12 hx hc).2
  have hrp := (lowGeometry31C_hz16 hx hc).2
  have hbn := (lowGeometry31C_hz21 hx hc).2
  have hlo := (lowGeometry31C_hz40 hx hc).1
  have hhi := (lowGeometry31C_hz35 hx hc).2
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
