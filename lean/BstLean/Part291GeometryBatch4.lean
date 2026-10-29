import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part199 BstLean.Part255 BstLean.Part264b
theorem lowGeometry128W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (131 / 250) (1049 / 2000) θ := hc

theorem lowGeometry128W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry128W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (951 / 2000) (119 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry128W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (124581 / 500000) (124831 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry128W_hz0 hx hc) (lowGeometry128W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (124831 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry128W_hz3 hx hc) (lowGeometry128W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (2793194855358287 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry128W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (8379584566074861 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry128W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (131 / 125) (1049 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry128W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry128W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry128W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1049 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry128W_hz7 hx hc) (lowGeometry128W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (14935834566074861 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry128W_hz6 hx hc) (lowGeometry128W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (14935834566074861 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry128W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry128W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (524 / 25) (1049 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry128W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1049 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry128W_hz13 hx hc) (lowGeometry128W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (15263647066074861 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry128W_hz12 hx hc) (lowGeometry128W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (15263647066074861 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry128W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry128W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1049 / 16000000) (θ * x) := bmul (lowGeometry128W_hz0 hx hc) (lowGeometry128W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (137881177707677 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry128W_hz17 hx hc) (lowGeometry128W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (11742281622737423 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry128W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (35226844868212269 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry128W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (35226844868212269 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry128W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry128W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (524 / 125) (1049 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry128W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry128W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (46912706167945591 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry128W_hz22 hx hc) (lowGeometry128W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry128W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry128W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry128W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry128W_hz26 hx hc) (lowGeometry128W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry128W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (49314158311787097 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry128W_hz24 hx hc) (lowGeometry128W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (535226844868212269 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry128W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (1145871101870325449 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry128W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (951 / 2000) (272717322245137457 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry128W_hz2 hx hc) (lowGeometry128W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (951 / 2000) (594748802802062011 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry128W_hz33 hx hc) (lowGeometry128W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (951 / 2000) (594748802802062011 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry128W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry128W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (464773155131787731 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry128W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (27001760716394603 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry128W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (410858791060660279 / 1000000000000000000) (119 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry128W_hz2 hx hc) (lowGeometry128W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (180772316374436591 / 500000000000000000) (119 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry128W_hz38 hx hc) (lowGeometry128W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (180772316374436591 / 500000000000000000) (119 / 250) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry128W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry128W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (131 / 250) (1049 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (322200941 / 1000000000) (84432113 / 125000000) ∧ radiusMinus n θ lowWideWindow ≤ (119486677 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry128W_hz12 hx hc).2
  have hrp := (lowGeometry128W_hz16 hx hc).2
  have hbn := (lowGeometry128W_hz21 hx hc).2
  have hlo := (lowGeometry128W_hz40 hx hc).1
  have hhi := (lowGeometry128W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry128C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (131 / 250) (1049 / 2000) θ := hc

theorem lowGeometry128C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry128C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (951 / 2000) (119 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry128C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (124581 / 500000) (124831 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry128C_hz0 hx hc) (lowGeometry128C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (124831 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry128C_hz3 hx hc) (lowGeometry128C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (2793194855358287 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry128C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (32177604733727467 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry128C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (131 / 125) (1049 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry128C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry128C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry128C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (8194001145083213 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry128C_hz7 hx hc) (lowGeometry128C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (64953609314060319 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry128C_hz6 hx hc) (lowGeometry128C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (64953609314060319 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry128C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry128C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (102311 / 12500) (819269 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry128C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (819269 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry128C_hz13 hx hc) (lowGeometry128C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (65977695564060319 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry128C_hz12 hx hc) (lowGeometry128C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (65977695564060319 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry128C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry128C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (1049 / 16000000) (θ * x) := bmul (lowGeometry128C_hz0 hx hc) (lowGeometry128C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (137881177707677 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry128C_hz17 hx hc) (lowGeometry128C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (11742281622737423 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry128C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (33817771073483779 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry128C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (33817771073483779 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry128C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry128C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (42837 / 25000) (343023 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry128C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry128C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (239694608076847 / 12500000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry128C_hz22 hx hc) (lowGeometry128C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry128C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry128C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry128C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry128C_hz26 hx hc) (lowGeometry128C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry128C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 0 (19783783678590799 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry128C_hz24 hx hc) (lowGeometry128C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (1033817771073483779 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry128C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B 1 (213755836757469223 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry128C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (951 / 2000) (508738891482776751 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry128C_hz2 hx hc) (lowGeometry128C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (951 / 2000) (10570453503227351 / 20000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry128C_hz33 hx hc) (lowGeometry128C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (951 / 2000) (10570453503227351 / 20000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry128C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry128C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (966182228926516221 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry128C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (466754049746705499 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry128C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (443883101309116929 / 1000000000000000000) (119 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry128C_hz2 hx hc) (lowGeometry128C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (42409931763052613 / 100000000000000000) (119 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry128C_hz38 hx hc) (lowGeometry128C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry128C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (131 / 250) (1049 / 2000) θ) : B (42409931763052613 / 100000000000000000) (119 / 250) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry128C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry128C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (131 / 250) (1049 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (79570017 / 200000000) (565236849 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (6495361 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry128C_hz12 hx hc).2
  have hrp := (lowGeometry128C_hz16 hx hc).2
  have hbn := (lowGeometry128C_hz21 hx hc).2
  have hlo := (lowGeometry128C_hz40 hx hc).1
  have hhi := (lowGeometry128C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry129W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (1049 / 2000) (21 / 40) θ := hc

theorem lowGeometry129W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry129W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19 / 40) (951 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry129W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19931 / 80000) (19971 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry129W_hz0 hx hc) (lowGeometry129W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (19971 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry129W_hz3 hx hc) (lowGeometry129W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (2793057800153803 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry129W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (8379173400461409 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry129W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (1049 / 1000) (21 / 20) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry129W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry129W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry129W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (21 / 400) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry129W_hz7 hx hc) (lowGeometry129W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (14941673400461409 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry129W_hz6 hx hc) (lowGeometry129W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (14941673400461409 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry129W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry129W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (1049 / 50) 21 (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry129W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (21 / 8000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry129W_hz13 hx hc) (lowGeometry129W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (15269798400461409 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry129W_hz12 hx hc) (lowGeometry129W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (15269798400461409 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry129W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry129W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (21 / 320000) (θ * x) := bmul (lowGeometry129W_hz0 hx hc) (lowGeometry129W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (138157894736843 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry129W_hz17 hx hc) (lowGeometry129W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (146925733119259 / 12500000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry129W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (440777199357777 / 6250000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry129W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (440777199357777 / 6250000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry129W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry129W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (1049 / 250) (21 / 5) (θ * (8 : ℝ)) := bmul (lowGeometry129W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry129W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (23478713763747793 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry129W_hz22 hx hc) (lowGeometry129W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry129W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry129W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry129W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry129W_hz26 hx hc) (lowGeometry129W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry129W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (12340292237220317 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry129W_hz24 hx hc) (lowGeometry129W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (6690777199357777 / 6250000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry129W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (1146022388005014989 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry129W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19 / 40) (136233411374096157 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry129W_hz2 hx hc) (lowGeometry129W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19 / 40) (74286851805658237 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry129W_hz33 hx hc) (lowGeometry129W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19 / 40) (74286851805658237 / 125000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry129W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry129W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (5809222800642223 / 6250000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry129W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (215981245104009427 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry129W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (410364365697617911 / 1000000000000000000) (951 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry129W_hz2 hx hc) (lowGeometry129W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (361003196748736643 / 1000000000000000000) (951 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry129W_hz38 hx hc) (lowGeometry129W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (361003196748736643 / 1000000000000000000) (951 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry129W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry129W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1049 / 2000) (21 / 40) θ) :
    OverlapGuard n θ lowWideWindow (80426079 / 250000000) (168744279 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (29883347 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry129W_hz12 hx hc).2
  have hrp := (lowGeometry129W_hz16 hx hc).2
  have hbn := (lowGeometry129W_hz21 hx hc).2
  have hlo := (lowGeometry129W_hz40 hx hc).1
  have hhi := (lowGeometry129W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry129C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (1049 / 2000) (21 / 40) θ := hc

theorem lowGeometry129C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry129C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19 / 40) (951 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry129C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19931 / 80000) (19971 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry129C_hz0 hx hc) (lowGeometry129C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (19971 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry129C_hz3 hx hc) (lowGeometry129C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (2793057800153803 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry129C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (32176025857771811 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry129C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (1049 / 1000) (21 / 20) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry129C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry129C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry129C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (8201812394983197 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry129C_hz7 hx hc) (lowGeometry129C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (64983275437704599 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry129C_hz6 hx hc) (lowGeometry129C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (64983275437704599 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry129C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry129C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (819269 / 100000) (16401 / 2000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry129C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (16401 / 16000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry129C_hz13 hx hc) (lowGeometry129C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (66008337937704599 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry129C_hz12 hx hc) (lowGeometry129C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (66008337937704599 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry129C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry129C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (21 / 320000) (θ * x) := bmul (lowGeometry129C_hz0 hx hc) (lowGeometry129C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (138157894736843 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry129C_hz17 hx hc) (lowGeometry129C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (146925733119259 / 12500000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry129C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (16925844455338637 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry129C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (16925844455338637 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry129C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry129C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (343023 / 200000) (6867 / 4000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry129C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry129C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (19193848501863821 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry129C_hz22 hx hc) (lowGeometry129C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry129C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry129C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry129C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry129C_hz26 hx hc) (lowGeometry129C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry129C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 0 (9901321669456787 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry129C_hz24 hx hc) (lowGeometry129C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (516925844455338637 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry129C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B 1 (1068849314663459819 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry129C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19 / 40) (63529731140309393 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry129C_hz2 hx hc) (lowGeometry129C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19 / 40) (264020246230694359 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry129C_hz33 hx hc) (lowGeometry129C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (19 / 40) (264020246230694359 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry129C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry129C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (483074155544661363 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry129C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (466721279510375361 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry129C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (27711575970928537 / 62500000000000000) (951 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry129C_hz2 hx hc) (lowGeometry129C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (211791286097971509 / 500000000000000000) (951 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry129C_hz38 hx hc) (lowGeometry129C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry129C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1049 / 2000) (21 / 40) θ) : B (211791286097971509 / 500000000000000000) (951 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry129C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry129C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1049 / 2000) (21 / 40) θ) :
    OverlapGuard n θ lowCoreWindow (397353901 / 1000000000) (564739089 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (16245819 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry129C_hz12 hx hc).2
  have hrp := (lowGeometry129C_hz16 hx hc).2
  have hbn := (lowGeometry129C_hz21 hx hc).2
  have hlo := (lowGeometry129C_hz40 hx hc).1
  have hhi := (lowGeometry129C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry130W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (21 / 40) (1051 / 2000) θ := hc

theorem lowGeometry130W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry130W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (949 / 2000) (19 / 40) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry130W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (19929 / 80000) (19969 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry130W_hz0 hx hc) (lowGeometry130W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (19969 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry130W_hz3 hx hc) (lowGeometry130W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1396458970485707 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry130W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (4189376911457121 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry130W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (21 / 20) (1051 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry130W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry130W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry130W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1051 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry130W_hz7 hx hc) (lowGeometry130W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (7473751911457121 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry130W_hz6 hx hc) (lowGeometry130W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (7473751911457121 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry130W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry130W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 21 (1051 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry130W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1051 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry130W_hz13 hx hc) (lowGeometry130W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (7637970661457121 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry130W_hz12 hx hc) (lowGeometry130W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (7637970661457121 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry130W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry130W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1051 / 16000000) (θ * x) := bmul (lowGeometry130W_hz0 hx hc) (lowGeometry130W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (27687038988409 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry130W_hz17 hx hc) (lowGeometry130W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (11765848670709861 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry130W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (35297546012129583 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry130W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (35297546012129583 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry130W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry130W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (21 / 5) (1051 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry130W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry130W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (23501074443522791 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry130W_hz22 hx hc) (lowGeometry130W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry130W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry130W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry130W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry130W_hz26 hx hc) (lowGeometry130W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry130W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (49408179585975441 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry130W_hz24 hx hc) (lowGeometry130W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (535297546012129583 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry130W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (1146173851066431953 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry130W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (949 / 2000) (272216289628277589 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry130W_hz2 hx hc) (lowGeometry130W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (949 / 2000) (593840758842530619 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry130W_hz33 hx hc) (lowGeometry130W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (949 / 2000) (593840758842530619 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry130W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry130W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (464702453987870417 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry130W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (107974185371174411 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry130W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (25616875479311129 / 62500000000000000) (19 / 40) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry130W_hz2 hx hc) (lowGeometry130W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (360461828083002623 / 1000000000000000000) (19 / 40) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry130W_hz38 hx hc) (lowGeometry130W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (360461828083002623 / 1000000000000000000) (19 / 40) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry130W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry130W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (21 / 40) (1051 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (160603907 / 500000000) (674497149 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (119580031 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry130W_hz12 hx hc).2
  have hrp := (lowGeometry130W_hz16 hx hc).2
  have hbn := (lowGeometry130W_hz21 hx hc).2
  have hlo := (lowGeometry130W_hz40 hx hc).1
  have hhi := (lowGeometry130W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry130C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (21 / 40) (1051 / 2000) θ := hc

theorem lowGeometry130C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry130C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (949 / 2000) (19 / 40) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry130C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (19929 / 80000) (19969 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry130C_hz0 hx hc) (lowGeometry130C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (19969 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry130C_hz3 hx hc) (lowGeometry130C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1396458970485707 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry130C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (3217441467999069 / 100000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry130C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (21 / 20) (1051 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry130C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry130C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry130C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (8209623644883181 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry130C_hz7 hx hc) (lowGeometry130C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (32506454629761707 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry130C_hz6 hx hc) (lowGeometry130C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (32506454629761707 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry130C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry130C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (16401 / 2000) (820831 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry130C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (820831 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry130C_hz13 hx hc) (lowGeometry130C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (33019474004761707 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry130C_hz12 hx hc) (lowGeometry130C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (33019474004761707 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry130C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry130C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (1051 / 16000000) (θ * x) := bmul (lowGeometry130C_hz0 hx hc) (lowGeometry130C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (27687038988409 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry130C_hz17 hx hc) (lowGeometry130C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (11765848670709861 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry130C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (84714110429111 / 2500000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry130C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (84714110429111 / 2500000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry130C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry130C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (6867 / 4000) (343677 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry130C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry130C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (9606064178789941 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry130C_hz22 hx hc) (lowGeometry130C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry130C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry130C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry130C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry130C_hz26 hx hc) (lowGeometry130C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry130C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 0 (19821502999236349 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry130C_hz24 hx hc) (lowGeometry130C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (2584714110429111 / 2500000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry130C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B 1 (1068919525224216099 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry130C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (949 / 2000) (63467096810187831 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry130C_hz2 hx hc) (lowGeometry130C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (949 / 2000) (527558277480738997 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry130C_hz33 hx hc) (lowGeometry130C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (949 / 2000) (527558277480738997 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry130C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry130C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (2415285889570889 / 2500000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry130C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (466688474268819249 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry130C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (442887362081109467 / 1000000000000000000) (19 / 40) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry130C_hz2 hx hc) (lowGeometry130C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (211532929540936559 / 500000000000000000) (19 / 40) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry130C_hz38 hx hc) (lowGeometry130C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry130C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (21 / 40) (1051 / 2000) θ) : B (211532929540936559 / 500000000000000000) (19 / 40) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry130C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry130C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (21 / 40) (1051 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (99214447 / 250000000) (564241243 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (6501291 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry130C_hz12 hx hc).2
  have hrp := (lowGeometry130C_hz16 hx hc).2
  have hbn := (lowGeometry130C_hz21 hx hc).2
  have hlo := (lowGeometry130C_hz40 hx hc).1
  have hhi := (lowGeometry130C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry131W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (1051 / 2000) (263 / 500) θ := hc

theorem lowGeometry131W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry131W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (237 / 500) (949 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry131W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (249087 / 1000000) (249587 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry131W_hz0 hx hc) (lowGeometry131W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (249587 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry131W_hz3 hx hc) (lowGeometry131W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (5585550554779717 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry131W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (16756651664339151 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry131W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (1051 / 1000) (263 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry131W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry131W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry131W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (263 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry131W_hz7 hx hc) (lowGeometry131W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (29906651664339151 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry131W_hz6 hx hc) (lowGeometry131W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (29906651664339151 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry131W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry131W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (1051 / 50) (526 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry131W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (263 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry131W_hz13 hx hc) (lowGeometry131W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (30564151664339151 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry131W_hz12 hx hc) (lowGeometry131W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (30564151664339151 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry131W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry131W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (263 / 4000000) (θ * x) := bmul (lowGeometry131W_hz0 hx hc) (lowGeometry131W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (138713080168777 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry131W_hz17 hx hc) (lowGeometry131W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (1177765172556809 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry131W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (3533295517670427 / 50000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry131W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (3533295517670427 / 50000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry131W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry131W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (1051 / 250) (526 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry131W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry131W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (23523435123297789 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry131W_hz22 hx hc) (lowGeometry131W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry131W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry131W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry131W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry131W_hz26 hx hc) (lowGeometry131W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry131W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (24727595111534807 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry131W_hz24 hx hc) (lowGeometry131W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (53533295517670427 / 50000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry131W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (1146325491592893053 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry131W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (237 / 500) (271965722880413877 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry131W_hz2 hx hc) (lowGeometry131W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (237 / 500) (74173329497987171 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry131W_hz33 hx hc) (lowGeometry131W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (237 / 500) (74173329497987171 / 125000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry131W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry131W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (46466704482329573 / 50000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry131W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (215915462544814723 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry131W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (204687858492484357 / 500000000000000000) (949 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry131W_hz2 hx hc) (lowGeometry131W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (3599205267618991 / 10000000000000000) (949 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry131W_hz38 hx hc) (lowGeometry131W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (3599205267618991 / 10000000000000000) (949 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry131W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry131W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1051 / 2000) (263 / 500) θ) :
    OverlapGuard n θ lowWideWindow (64142287 / 200000000) (674017003 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (119626607 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry131W_hz12 hx hc).2
  have hrp := (lowGeometry131W_hz16 hx hc).2
  have hbn := (lowGeometry131W_hz21 hx hc).2
  have hlo := (lowGeometry131W_hz40 hx hc).1
  have hhi := (lowGeometry131W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry131C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (1051 / 2000) (263 / 500) θ := hc

theorem lowGeometry131C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry131C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (237 / 500) (949 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry131C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (249087 / 1000000) (249587 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry131C_hz0 hx hc) (lowGeometry131C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (249587 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry131C_hz3 hx hc) (lowGeometry131C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (5585550554779717 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry131C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (3217277119553117 / 100000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry131C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (1051 / 1000) (263 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry131C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry131C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry131C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (1643486978956633 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry131C_hz7 hx hc) (lowGeometry131C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (6504251077466383 / 100000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry131C_hz6 hx hc) (lowGeometry131C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (6504251077466383 / 100000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry131C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry131C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (820831 / 100000) (205403 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry131C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (205403 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry131C_hz13 hx hc) (lowGeometry131C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (6606952577466383 / 100000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry131C_hz12 hx hc) (lowGeometry131C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (6606952577466383 / 100000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry131C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry131C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (263 / 4000000) (θ * x) := bmul (lowGeometry131C_hz0 hx hc) (lowGeometry131C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (138713080168777 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry131C_hz17 hx hc) (lowGeometry131C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (1177765172556809 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry131C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (339196369696361 / 10000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry131C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (339196369696361 / 10000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry131C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry131C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (343677 / 200000) (86001 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry131C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry131C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (19230408213295943 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry131C_hz22 hx hc) (lowGeometry131C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry131C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry131C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry131C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry131C_hz26 hx hc) (lowGeometry131C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry131C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 0 (4960090664889781 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry131C_hz24 hx hc) (lowGeometry131C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (10339196369696361 / 10000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry131C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B 1 (213797963142284821 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry131C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (237 / 500) (253617833777535369 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry131C_hz2 hx hc) (lowGeometry131C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (237 / 500) (263538015107314931 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry131C_hz33 hx hc) (lowGeometry131C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (237 / 500) (263538015107314931 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry131C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry131C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (9660803630303639 / 10000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry131C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (116663908479109963 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry131C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (442389540952784979 / 1000000000000000000) (949 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry131C_hz2 hx hc) (lowGeometry131C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (84509835658645171 / 200000000000000000) (949 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry131C_hz38 hx hc) (lowGeometry131C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry131C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1051 / 2000) (263 / 500) θ) : B (84509835658645171 / 200000000000000000) (949 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry131C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry131C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1051 / 2000) (263 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (79272349 / 200000000) (563743311 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65042511 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry131C_hz12 hx hc).2
  have hrp := (lowGeometry131C_hz16 hx hc).2
  have hbn := (lowGeometry131C_hz21 hx hc).2
  have hlo := (lowGeometry131C_hz40 hx hc).1
  have hhi := (lowGeometry131C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry132W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (263 / 500) (1053 / 2000) θ := hc

theorem lowGeometry132W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry132W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (947 / 2000) (237 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry132W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (249061 / 1000000) (249561 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry132W_hz0 hx hc) (lowGeometry132W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (249561 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry132W_hz3 hx hc) (lowGeometry132W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (2792629808979343 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry132W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (8377889426938029 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry132W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (263 / 250) (1053 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry132W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry132W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry132W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1053 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry132W_hz7 hx hc) (lowGeometry132W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (14959139426938029 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry132W_hz6 hx hc) (lowGeometry132W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (14959139426938029 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry132W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry132W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (526 / 25) (1053 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry132W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1053 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry132W_hz13 hx hc) (lowGeometry132W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (15288201926938029 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry132W_hz12 hx hc) (lowGeometry132W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (15288201926938029 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry132W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry132W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1053 / 16000000) (θ * x) := bmul (lowGeometry132W_hz0 hx hc) (lowGeometry132W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (17373944033791 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry132W_hz17 hx hc) (lowGeometry132W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (94315742828549 / 8000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry132W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (282947228485647 / 4000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry132W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (282947228485647 / 4000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry132W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry132W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (526 / 125) (1053 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry132W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry132W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (23545795803072787 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry132W_hz22 hx hc) (lowGeometry132W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry132W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry132W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry132W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry132W_hz26 hx hc) (lowGeometry132W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry132W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (49502200860163787 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry132W_hz24 hx hc) (lowGeometry132W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (4282947228485647 / 4000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry132W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (1146477310124555309 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry132W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (947 / 2000) (543430244999039217 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry132W_hz2 hx hc) (lowGeometry132W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (947 / 2000) (148233111464800751 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry132W_hz33 hx hc) (lowGeometry132W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (947 / 2000) (148233111464800751 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry132W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry132W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (3717052771514353 / 4000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry132W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (215882520409727077 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry132W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (408881493656023083 / 1000000000000000000) (237 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry132W_hz2 hx hc) (lowGeometry132W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (11230602899870603 / 31250000000000000) (237 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry132W_hz38 hx hc) (lowGeometry132W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (11230602899870603 / 31250000000000000) (237 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry132W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry132W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (263 / 500) (1053 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (160107589 / 500000000) (673536679 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (29918279 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry132W_hz12 hx hc).2
  have hrp := (lowGeometry132W_hz16 hx hc).2
  have hbn := (lowGeometry132W_hz21 hx hc).2
  have hlo := (lowGeometry132W_hz40 hx hc).1
  have hhi := (lowGeometry132W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry132C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (263 / 500) (1053 / 2000) θ := hc

theorem lowGeometry132C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry132C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (947 / 2000) (237 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry132C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (249061 / 1000000) (249561 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry132C_hz0 hx hc) (lowGeometry132C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (249561 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry132C_hz3 hx hc) (lowGeometry132C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (2792629808979343 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry132C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (2010693462465127 / 62500000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry132C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (263 / 250) (1053 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry132C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry132C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry132C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (8225246144683149 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry132C_hz7 hx hc) (lowGeometry132C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (16268019994543657 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry132C_hz6 hx hc) (lowGeometry132C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (16268019994543657 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry132C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry132C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (205403 / 25000) (822393 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry132C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (822393 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry132C_hz13 hx hc) (lowGeometry132C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (16525017807043657 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry132C_hz12 hx hc) (lowGeometry132C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (16525017807043657 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry132C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry132C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (1053 / 16000000) (θ * x) := bmul (lowGeometry132C_hz0 hx hc) (lowGeometry132C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (17373944033791 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry132C_hz17 hx hc) (lowGeometry132C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (94315742828549 / 8000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry132C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (848841685456941 / 25000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry132C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (848841685456941 / 25000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry132C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry132C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (86001 / 50000) (344331 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry132C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry132C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (4812172017253001 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry132C_hz22 hx hc) (lowGeometry132C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry132C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry132C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry132C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry132C_hz26 hx hc) (lowGeometry132C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry132C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 0 (19859222319881899 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry132C_hz24 hx hc) (lowGeometry132C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (25848841685456941 / 25000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry132C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B 1 (1069060186367706289 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry132C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (947 / 2000) (506734528338292781 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry132C_hz2 hx hc) (lowGeometry132C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (947 / 2000) (13164843766454367 / 25000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry132C_hz33 hx hc) (lowGeometry132C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (947 / 2000) (13164843766454367 / 25000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry132C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry132C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (24151158314543059 / 25000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry132C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (58327844793412233 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry132C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (441891752154891077 / 1000000000000000000) (237 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry132C_hz2 hx hc) (lowGeometry132C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (211016264917504589 / 500000000000000000) (237 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry132C_hz38 hx hc) (lowGeometry132C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry132C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (263 / 500) (1053 / 2000) θ) : B (211016264917504589 / 500000000000000000) (237 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry132C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry132C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (263 / 500) (1053 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (395865773 / 1000000000) (281622647 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (813401 / 12500000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry132C_hz12 hx hc).2
  have hrp := (lowGeometry132C_hz16 hx hc).2
  have hbn := (lowGeometry132C_hz21 hx hc).2
  have hlo := (lowGeometry132C_hz40 hx hc).1
  have hhi := (lowGeometry132C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry133W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (1053 / 2000) (527 / 1000) θ := hc

theorem lowGeometry133W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry133W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (473 / 1000) (947 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry133W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (498069 / 2000000) (499069 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry133W_hz0 hx hc) (lowGeometry133W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (499069 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry133W_hz3 hx hc) (lowGeometry133W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (698120383825383 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry133W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (2094361151476149 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry133W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (1053 / 1000) (527 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry133W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry133W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry133W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (527 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry133W_hz7 hx hc) (lowGeometry133W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (3741236151476149 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry133W_hz6 hx hc) (lowGeometry133W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (3741236151476149 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry133W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry133W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (1053 / 50) (527 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry133W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (527 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry133W_hz13 hx hc) (lowGeometry133W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (3823579901476149 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry133W_hz12 hx hc) (lowGeometry133W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (3823579901476149 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry133W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry133W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (527 / 8000000) (θ * x) := bmul (lowGeometry133W_hz0 hx hc) (lowGeometry133W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (139270613107823 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry133W_hz17 hx hc) (lowGeometry133W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (5900648547147657 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry133W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (17701945641442971 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry133W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (17701945641442971 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry133W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry133W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (1053 / 250) (527 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry133W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry133W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (47136312965695569 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry133W_hz22 hx hc) (lowGeometry133W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry133W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry133W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry133W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry133W_hz26 hx hc) (lowGeometry133W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry133W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (49549211497257959 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry133W_hz24 hx hc) (lowGeometry133W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (267701945641442971 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry133W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (1146629307203425397 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry133W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (473 / 1000) (271464488480410963 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry133W_hz2 hx hc) (lowGeometry133W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (473 / 1000) (118495637691615977 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry133W_hz33 hx hc) (lowGeometry133W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (473 / 1000) (118495637691615977 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry133W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry133W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (232298054358557029 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry133W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (43169908847016893 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry133W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (408387337692779807 / 1000000000000000000) (947 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry133W_hz2 hx hc) (lowGeometry133W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (44854765774440231 / 125000000000000000) (947 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry133W_hz38 hx hc) (lowGeometry133W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (44854765774440231 / 125000000000000000) (947 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry133W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry133W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1053 / 2000) (527 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (79929761 / 250000000) (42066011 / 62500000) ∧ radiusMinus n θ lowWideWindow ≤ (119719557 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry133W_hz12 hx hc).2
  have hrp := (lowGeometry133W_hz16 hx hc).2
  have hbn := (lowGeometry133W_hz21 hx hc).2
  have hlo := (lowGeometry133W_hz40 hx hc).1
  have hhi := (lowGeometry133W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry133C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (1053 / 2000) (527 / 1000) θ := hc

theorem lowGeometry133C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry133C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (473 / 1000) (947 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry133C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (498069 / 2000000) (499069 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry133C_hz0 hx hc) (lowGeometry133C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (499069 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry133C_hz3 hx hc) (lowGeometry133C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (698120383825383 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry133C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (32169387286673649 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry133C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (1053 / 1000) (527 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry133C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry133C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry133C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (8233057394583133 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry133C_hz7 hx hc) (lowGeometry133C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (65101616865006181 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry133C_hz6 hx hc) (lowGeometry133C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (65101616865006181 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry133C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry133C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (822393 / 100000) (411587 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry133C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (411587 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry133C_hz13 hx hc) (lowGeometry133C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (66130584365006181 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry133C_hz12 hx hc) (lowGeometry133C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (66130584365006181 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry133C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry133C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (527 / 8000000) (θ * x) := bmul (lowGeometry133C_hz0 hx hc) (lowGeometry133C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (139270613107823 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry133C_hz17 hx hc) (lowGeometry133C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (5900648547147657 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry133C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (6797547126314101 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry133C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (6797547126314101 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry133C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry133C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (344331 / 200000) (172329 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry133C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry133C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (75261593455969 / 3906250000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry133C_hz22 hx hc) (lowGeometry133C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry133C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry133C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry133C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry133C_hz26 hx hc) (lowGeometry133C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry133C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 0 (19878081980204673 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry133C_hz24 hx hc) (lowGeometry133C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (206797547126314101 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry133C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B 1 (534565318718251269 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry133C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (473 / 1000) (31639584801636497 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry133C_hz2 hx hc) (lowGeometry133C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (473 / 1000) (4208891510451109 / 8000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry133C_hz33 hx hc) (lowGeometry133C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (473 / 1000) (4208891510451109 / 8000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry133C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry133C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (193202452873685899 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry133C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (933179694910220517 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry133C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (13793562365391697 / 31250000000000000) (947 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry133C_hz2 hx hc) (lowGeometry133C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (421515913712329631 / 1000000000000000000) (947 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry133C_hz38 hx hc) (lowGeometry133C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry133C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1053 / 2000) (527 / 1000) θ) : B (421515913712329631 / 1000000000000000000) (947 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry133C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry133C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1053 / 2000) (527 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (24710617 / 62500000) (562747191 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65101617 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry133C_hz12 hx hc).2
  have hrp := (lowGeometry133C_hz16 hx hc).2
  have hbn := (lowGeometry133C_hz21 hx hc).2
  have hlo := (lowGeometry133C_hz40 hx hc).1
  have hhi := (lowGeometry133C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry134W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (527 / 1000) (211 / 400) θ := hc

theorem lowGeometry134W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry134W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (189 / 400) (473 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry134W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (99603 / 400000) (99803 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry134W_hz0 hx hc) (lowGeometry134W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (99803 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry134W_hz3 hx hc) (lowGeometry134W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (349041306988693 / 62500000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry134W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1047123920966079 / 15625000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry134W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (527 / 500) (211 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry134W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry134W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry134W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (211 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry134W_hz7 hx hc) (lowGeometry134W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1871342670966079 / 15625000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry134W_hz6 hx hc) (lowGeometry134W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1871342670966079 / 15625000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry134W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry134W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (527 / 25) (211 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry134W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (211 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry134W_hz13 hx hc) (lowGeometry134W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1912553608466079 / 15625000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry134W_hz12 hx hc) (lowGeometry134W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1912553608466079 / 15625000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry134W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry134W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (211 / 3200000) (θ * x) := bmul (lowGeometry134W_hz0 hx hc) (lowGeometry134W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (27910052910053 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry134W_hz17 hx hc) (lowGeometry134W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (5906569743731657 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry134W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (17719709231194971 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry134W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (17719709231194971 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry134W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry134W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (527 / 125) (211 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry134W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry134W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (9436206865049113 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry134W_hz22 hx hc) (lowGeometry134W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry134W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry134W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry134W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry134W_hz26 hx hc) (lowGeometry134W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry134W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (12399055533588033 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry134W_hz24 hx hc) (lowGeometry134W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (267719709231194971 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry134W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (1146781483373369309 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry134W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (189 / 400) (135606910408900921 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry134W_hz2 hx hc) (lowGeometry134W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (189 / 400) (74002982971244477 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry134W_hz33 hx hc) (lowGeometry134W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (189 / 400) (74002982971244477 / 125000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry134W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry134W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (232280290768805029 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry134W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (215816533918562443 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry134W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (407893249106083017 / 1000000000000000000) (473 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry134W_hz2 hx hc) (lowGeometry134W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (71659405394346177 / 200000000000000000) (473 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry134W_hz38 hx hc) (lowGeometry134W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (71659405394346177 / 200000000000000000) (473 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry134W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry134W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (527 / 1000) (211 / 400) θ) :
    OverlapGuard n θ lowWideWindow (39902879 / 125000000) (336287747 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (119765931 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry134W_hz12 hx hc).2
  have hrp := (lowGeometry134W_hz16 hx hc).2
  have hbn := (lowGeometry134W_hz21 hx hc).2
  have hlo := (lowGeometry134W_hz40 hx hc).1
  have hhi := (lowGeometry134W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry134C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (527 / 1000) (211 / 400) θ := hc

theorem lowGeometry134C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry134C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (189 / 400) (473 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry134C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (99603 / 400000) (99803 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry134C_hz0 hx hc) (lowGeometry134C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (99803 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry134C_hz3 hx hc) (lowGeometry134C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (349041306988693 / 62500000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry134C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (32167646852077947 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry134C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (527 / 500) (211 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry134C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry134C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry134C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (8240868644483117 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry134C_hz7 hx hc) (lowGeometry134C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (13026224286002083 / 200000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry134C_hz6 hx hc) (lowGeometry134C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (13026224286002083 / 200000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry134C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry134C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (411587 / 50000) (164791 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry134C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (164791 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry134C_hz13 hx hc) (lowGeometry134C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (13232213036002083 / 200000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry134C_hz12 hx hc) (lowGeometry134C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (13232213036002083 / 200000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry134C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry134C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (211 / 3200000) (θ * x) := bmul (lowGeometry134C_hz0 hx hc) (lowGeometry134C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (27910052910053 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry134C_hz17 hx hc) (lowGeometry134C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (5906569743731657 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry134C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (6804368344778869 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry134C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (6804368344778869 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry134C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry134C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (172329 / 100000) (68997 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry134C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry134C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (154281982243553 / 8000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry134C_hz22 hx hc) (lowGeometry134C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry134C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry134C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry134C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry134C_hz26 hx hc) (lowGeometry134C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry134C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 0 (2487117705065931 / 125000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry134C_hz24 hx hc) (lowGeometry134C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (206804368344778869 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry134C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B 1 (1069201169162074409 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry134C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (189 / 400) (126433038253415299 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry134C_hz2 hx hc) (lowGeometry134C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (189 / 400) (131407273663547161 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry134C_hz33 hx hc) (lowGeometry134C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (189 / 400) (131407273663547161 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry134C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry134C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (193195631655221131 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry134C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (233278450566624257 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry134C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (88179254314183969 / 200000000000000000) (473 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry134C_hz2 hx hc) (lowGeometry134C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (420999329930392397 / 1000000000000000000) (473 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry134C_hz38 hx hc) (lowGeometry134C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry134C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (527 / 1000) (211 / 400) θ) : B (420999329930392397 / 1000000000000000000) (473 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry134C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry134C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (527 / 1000) (211 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (197437021 / 500000000) (562249003 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32565561 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry134C_hz12 hx hc).2
  have hrp := (lowGeometry134C_hz16 hx hc).2
  have hbn := (lowGeometry134C_hz21 hx hc).2
  have hlo := (lowGeometry134C_hz40 hx hc).1
  have hhi := (lowGeometry134C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry135W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (211 / 400) (66 / 125) θ := hc

theorem lowGeometry135W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry135W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (59 / 125) (189 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry135W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (12449 / 50000) (6237 / 25000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry135W_hz0 hx hc) (lowGeometry135W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (6237 / 200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry135W_hz3 hx hc) (lowGeometry135W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (2792176570347943 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry135W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (8376529711043829 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry135W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (211 / 200) (132 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry135W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry135W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry135W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (33 / 625) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry135W_hz7 hx hc) (lowGeometry135W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (14976529711043829 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry135W_hz6 hx hc) (lowGeometry135W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (14976529711043829 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry135W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry135W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (211 / 10) (528 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry135W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (33 / 12500) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry135W_hz13 hx hc) (lowGeometry135W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (15306529711043829 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry135W_hz12 hx hc) (lowGeometry135W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (15306529711043829 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry135W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry135W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (33 / 500000) (θ * x) := bmul (lowGeometry135W_hz0 hx hc) (lowGeometry135W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (139830508474577 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry135W_hz17 hx hc) (lowGeometry135W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (11824995072919777 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry135W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (35474985218759331 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry135W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (35474985218759331 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry135W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry135W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (211 / 50) (528 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry135W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry135W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (47225755684795561 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry135W_hz22 hx hc) (lowGeometry135W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry135W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry135W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry135W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry135W_hz26 hx hc) (lowGeometry135W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry135W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (1551351024107697 / 31250000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry135W_hz24 hx hc) (lowGeometry135W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (535474985218759331 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry135W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (1146933839180122097 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry135W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (59 / 125) (541926239012607691 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry135W_hz2 hx hc) (lowGeometry135W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (59 / 125) (118313894356810799 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry135W_hz33 hx hc) (lowGeometry135W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (59 / 125) (118313894356810799 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry135W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry135W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (464525014781240669 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry135W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (107891744678755931 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry135W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (81479845581396479 / 200000000000000000) (189 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry135W_hz2 hx hc) (lowGeometry135W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (357755995135536091 / 1000000000000000000) (189 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry135W_hz38 hx hc) (lowGeometry135W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (357755995135536091 / 1000000000000000000) (189 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry135W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry135W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (211 / 400) (66 / 125) θ) :
    OverlapGuard n θ lowWideWindow (318727143 / 1000000000) (336047317 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (59906119 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry135W_hz12 hx hc).2
  have hrp := (lowGeometry135W_hz16 hx hc).2
  have hbn := (lowGeometry135W_hz21 hx hc).2
  have hlo := (lowGeometry135W_hz40 hx hc).1
  have hhi := (lowGeometry135W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry135C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (211 / 400) (66 / 125) θ := hc

theorem lowGeometry135C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry135C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (59 / 125) (189 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry135C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (12449 / 50000) (6237 / 25000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry135C_hz0 hx hc) (lowGeometry135C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (6237 / 200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry135C_hz3 hx hc) (lowGeometry135C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (2792176570347943 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry135C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (2010367130650519 / 62500000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry135C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (211 / 200) (132 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry135C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry135C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry135C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (8248679894383101 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry135C_hz7 hx hc) (lowGeometry135C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (16290148416985177 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry135C_hz6 hx hc) (lowGeometry135C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (16290148416985177 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry135C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry135C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (164791 / 20000) (25773 / 3125) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry135C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (25773 / 25000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry135C_hz13 hx hc) (lowGeometry135C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (16547878416985177 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry135C_hz12 hx hc) (lowGeometry135C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (16547878416985177 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry135C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry135C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (33 / 500000) (θ * x) := bmul (lowGeometry135C_hz0 hx hc) (lowGeometry135C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (139830508474577 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry135C_hz17 hx hc) (lowGeometry135C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (11824995072919777 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry135C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (17027992905004479 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry135C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (17027992905004479 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry135C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry135C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (68997 / 40000) (10791 / 6250) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry135C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry135C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (9651763818080093 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry135C_hz22 hx hc) (lowGeometry135C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry135C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry135C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry135C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry135C_hz26 hx hc) (lowGeometry135C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry135C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 0 (19915801300850223 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry135C_hz24 hx hc) (lowGeometry135C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (517027992905004479 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry135C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B 1 (133658972723688681 / 125000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry135C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (59 / 125) (101046183379108643 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry135C_hz2 hx hc) (lowGeometry135C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (59 / 125) (262573359098196719 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry135C_hz33 hx hc) (lowGeometry135C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (59 / 125) (262573359098196719 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry135C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry135C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (482972007094995521 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry135C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (186609567709894723 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry135C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (220199289897675773 / 500000000000000000) (189 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry135C_hz2 hx hc) (lowGeometry135C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (420482778494501323 / 1000000000000000000) (189 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry135C_hz38 hx hc) (lowGeometry135C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry135C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (211 / 400) (66 / 125) θ) : B (420482778494501323 / 1000000000000000000) (189 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry135C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry135C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (211 / 400) (66 / 125) θ) :
    OverlapGuard n θ lowCoreWindow (197189141 / 500000000) (56175073 / 100000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32580297 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry135C_hz12 hx hc).2
  have hrp := (lowGeometry135C_hz16 hx hc).2
  have hbn := (lowGeometry135C_hz21 hx hc).2
  have hlo := (lowGeometry135C_hz40 hx hc).1
  have hhi := (lowGeometry135C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry136W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (66 / 125) (1057 / 2000) θ := hc

theorem lowGeometry136W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry136W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (943 / 2000) (59 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry136W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (31119 / 125000) (62363 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry136W_hz0 hx hc) (lowGeometry136W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (62363 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry136W_hz3 hx hc) (lowGeometry136W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (2792019878152733 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry136W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (8376059634458199 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry136W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (132 / 125) (1057 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry136W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry136W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry136W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1057 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry136W_hz7 hx hc) (lowGeometry136W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (14982309634458199 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry136W_hz6 hx hc) (lowGeometry136W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (14982309634458199 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry136W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry136W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (528 / 25) (1057 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry136W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1057 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry136W_hz13 hx hc) (lowGeometry136W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (15312622134458199 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry136W_hz12 hx hc) (lowGeometry136W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (15312622134458199 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry136W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry136W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1057 / 16000000) (θ * x) := bmul (lowGeometry136W_hz0 hx hc) (lowGeometry136W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (70055673382821 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry136W_hz17 hx hc) (lowGeometry136W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (11836863890644431 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry136W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (35510591671933293 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry136W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (35510591671933293 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry136W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry136W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (528 / 125) (1057 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry136W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry136W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (47270477044345557 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry136W_hz22 hx hc) (lowGeometry136W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry136W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry136W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry136W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry136W_hz26 hx hc) (lowGeometry136W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry136W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (49690243408540477 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry136W_hz24 hx hc) (lowGeometry136W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (535510591671933293 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry136W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (229417275034259257 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry136W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (943 / 2000) (541424769080851847 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry136W_hz2 hx hc) (lowGeometry136W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (943 / 2000) (147778753122348081 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry136W_hz33 hx hc) (lowGeometry136W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (943 / 2000) (147778753122348081 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry136W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry136W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (464489408328066707 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry136W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (43150082089791497 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry136W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (50863159263341727 / 125000000000000000) (59 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry136W_hz2 hx hc) (lowGeometry136W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (357215030698193339 / 1000000000000000000) (59 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry136W_hz38 hx hc) (lowGeometry136W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (357215030698193339 / 1000000000000000000) (59 / 125) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry136W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry136W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (66 / 125) (1057 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (19889461 / 62500000) (167903399 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (59929239 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry136W_hz12 hx hc).2
  have hrp := (lowGeometry136W_hz16 hx hc).2
  have hbn := (lowGeometry136W_hz21 hx hc).2
  have hlo := (lowGeometry136W_hz40 hx hc).1
  have hhi := (lowGeometry136W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry136C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (66 / 125) (1057 / 2000) θ := hc

theorem lowGeometry136C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry136C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (943 / 2000) (59 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry136C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (31119 / 125000) (62363 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry136C_hz0 hx hc) (lowGeometry136C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (62363 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry136C_hz3 hx hc) (lowGeometry136C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (2792019878152733 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry136C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (6432813799263897 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry136C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (132 / 125) (1057 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry136C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry136C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry136C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1651298228856617 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry136C_hz7 hx hc) (lowGeometry136C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (2607601342938073 / 40000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry136C_hz6 hx hc) (lowGeometry136C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (2607601342938073 / 40000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry136C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry136C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (25773 / 3125) (825517 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry136C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (825517 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry136C_hz13 hx hc) (lowGeometry136C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (2648877192938073 / 40000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry136C_hz12 hx hc) (lowGeometry136C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (2648877192938073 / 40000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry136C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry136C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (1057 / 16000000) (θ * x) := bmul (lowGeometry136C_hz0 hx hc) (lowGeometry136C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (70055673382821 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry136C_hz17 hx hc) (lowGeometry136C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (11836863890644431 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry136C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (17045084002527981 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry136C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (17045084002527981 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry136C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry136C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (10791 / 6250) (345639 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry136C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry136C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (19321807491876247 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry136C_hz22 hx hc) (lowGeometry136C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry136C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry136C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry136C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry136C_hz26 hx hc) (lowGeometry136C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry136C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 0 (9967330480586499 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry136C_hz24 hx hc) (lowGeometry136C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (517045084002527981 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry136C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B 1 (534671237782362433 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry136C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (943 / 2000) (504729648466550137 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry136C_hz2 hx hc) (lowGeometry136C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (943 / 2000) (104932861885544627 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry136C_hz33 hx hc) (lowGeometry136C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (943 / 2000) (104932861885544627 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry136C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry136C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (482954915997472019 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry136C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (932981803544501017 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry136C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (439900920371232229 / 1000000000000000000) (59 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry136C_hz2 hx hc) (lowGeometry136C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (419966259410059231 / 1000000000000000000) (59 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry136C_hz38 hx hc) (lowGeometry136C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry136C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (66 / 125) (1057 / 2000) θ) : B (419966259410059231 / 1000000000000000000) (59 / 125) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry136C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry136C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (66 / 125) (1057 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (393882593 / 1000000000) (561252371 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32595017 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry136C_hz12 hx hc).2
  have hrp := (lowGeometry136C_hz16 hx hc).2
  have hbn := (lowGeometry136C_hz21 hx hc).2
  have hlo := (lowGeometry136C_hz40 hx hc).1
  have hhi := (lowGeometry136C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry137W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (1057 / 2000) (529 / 1000) θ := hc

theorem lowGeometry137W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry137W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (471 / 1000) (943 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry137W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (497847 / 2000000) (498847 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry137W_hz0 hx hc) (lowGeometry137W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (498847 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry137W_hz3 hx hc) (lowGeometry137W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (5583720757702699 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry137W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (16751162273108097 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry137W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (1057 / 1000) (529 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry137W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry137W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry137W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (529 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry137W_hz7 hx hc) (lowGeometry137W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (29976162273108097 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry137W_hz6 hx hc) (lowGeometry137W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (29976162273108097 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry137W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry137W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (1057 / 50) (529 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry137W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (529 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry137W_hz13 hx hc) (lowGeometry137W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (30637412273108097 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry137W_hz12 hx hc) (lowGeometry137W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (30637412273108097 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry137W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry137W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (529 / 8000000) (θ * x) := bmul (lowGeometry137W_hz0 hx hc) (lowGeometry137W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (140392781316349 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry137W_hz17 hx hc) (lowGeometry137W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (11848745980750411 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry137W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (35546237942251233 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry137W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (35546237942251233 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry137W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry137W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (1057 / 250) (529 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry137W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry137W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (47315198403895553 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry137W_hz22 hx hc) (lowGeometry137W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry137W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry137W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry137W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry137W_hz26 hx hc) (lowGeometry137W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry137W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (994745080912693 / 20000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry137W_hz24 hx hc) (lowGeometry137W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (535546237942251233 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry137W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (1147239091896393497 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry137W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (471 / 1000) (270461615914574767 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry137W_hz2 hx hc) (lowGeometry137W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (471 / 1000) (73832560734348023 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry137W_hz33 hx hc) (lowGeometry137W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (471 / 1000) (73832560734348023 / 125000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry137W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry137W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (464453762057748767 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry137W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (53929324272398977 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry137W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (40641138771679869 / 100000000000000000) (943 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry137W_hz2 hx hc) (lowGeometry137W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (8916853341779101 / 25000000000000000) (943 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry137W_hz38 hx hc) (lowGeometry137W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (8916853341779101 / 25000000000000000) (943 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry137W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry137W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1057 / 2000) (529 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (317735731 / 1000000000) (671132379 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (2398093 / 20000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry137W_hz12 hx hc).2
  have hrp := (lowGeometry137W_hz16 hx hc).2
  have hbn := (lowGeometry137W_hz21 hx hc).2
  have hlo := (lowGeometry137W_hz40 hx hc).1
  have hhi := (lowGeometry137W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry137C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (1057 / 2000) (529 / 1000) θ := hc

theorem lowGeometry137C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry137C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (471 / 1000) (943 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry137C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (497847 / 2000000) (498847 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry137C_hz0 hx hc) (lowGeometry137C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (498847 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry137C_hz3 hx hc) (lowGeometry137C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (5583720757702699 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry137C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (32162231564367547 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry137C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (1057 / 1000) (529 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry137C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry137C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry137C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (8264302394183069 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry137C_hz7 hx hc) (lowGeometry137C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (65219441141099823 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry137C_hz6 hx hc) (lowGeometry137C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (65219441141099823 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry137C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry137C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (825517 / 100000) (413149 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry137C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (413149 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry137C_hz13 hx hc) (lowGeometry137C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (66252313641099823 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry137C_hz12 hx hc) (lowGeometry137C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (66252313641099823 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry137C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry137C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (529 / 8000000) (θ * x) := bmul (lowGeometry137C_hz0 hx hc) (lowGeometry137C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (140392781316349 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry137C_hz17 hx hc) (lowGeometry137C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (11848745980750411 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry137C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (1066387138267537 / 31250000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry137C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (1066387138267537 / 31250000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry137C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry137C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (345639 / 200000) (172983 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry137C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry137C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (19340087347592307 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry137C_hz22 hx hc) (lowGeometry137C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry137C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry137C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry137C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry137C_hz26 hx hc) (lowGeometry137C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry137C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 0 (4988380155373943 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry137C_hz24 hx hc) (lowGeometry137C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (32316387138267537 / 31250000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry137C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B 1 (534706625367236347 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry137C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (471 / 1000) (126057086930325969 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry137C_hz2 hx hc) (lowGeometry137C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (471 / 1000) (16380683385712489 / 31250000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry137C_hz33 hx hc) (lowGeometry137C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (471 / 1000) (16380683385712489 / 31250000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry137C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry137C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (30183612861732463 / 31250000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry137C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (932915697036227957 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry137C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (439403293304063367 / 1000000000000000000) (943 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry137C_hz2 hx hc) (lowGeometry137C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (83889954536513519 / 200000000000000000) (943 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry137C_hz38 hx hc) (lowGeometry137C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry137C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1057 / 2000) (529 / 1000) θ) : B (83889954536513519 / 200000000000000000) (943 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry137C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry137C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1057 / 2000) (529 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (15735479 / 40000000) (560753927 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32609721 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry137C_hz12 hx hc).2
  have hrp := (lowGeometry137C_hz16 hx hc).2
  have hbn := (lowGeometry137C_hz21 hx hc).2
  have hlo := (lowGeometry137C_hz40 hx hc).1
  have hhi := (lowGeometry137C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry138W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (529 / 1000) (1059 / 2000) θ := hc

theorem lowGeometry138W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry138W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (941 / 2000) (471 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry138W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (497789 / 2000000) (498789 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry138W_hz0 hx hc) (lowGeometry138W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (498789 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry138W_hz3 hx hc) (lowGeometry138W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (5583396143925309 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry138W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (16750188431775927 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry138W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (529 / 500) (1059 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry138W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry138W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry138W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1059 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry138W_hz7 hx hc) (lowGeometry138W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (29987688431775927 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry138W_hz6 hx hc) (lowGeometry138W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (29987688431775927 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry138W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry138W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (529 / 25) (1059 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry138W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1059 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry138W_hz13 hx hc) (lowGeometry138W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (30649563431775927 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry138W_hz12 hx hc) (lowGeometry138W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (30649563431775927 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry138W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry138W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1059 / 16000000) (θ * x) := bmul (lowGeometry138W_hz0 hx hc) (lowGeometry138W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (140674814027631 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry138W_hz17 hx hc) (lowGeometry138W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (11860641383484749 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry138W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (35581924150454247 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry138W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (35581924150454247 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry138W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry138W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (529 / 125) (1059 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry138W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry138W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (11839979940861387 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry138W_hz22 hx hc) (lowGeometry138W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry138W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry138W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry138W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry138W_hz26 hx hc) (lowGeometry138W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry138W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (24892132341364411 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry138W_hz24 hx hc) (lowGeometry138W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (535581924150454247 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry138W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (229478397981362341 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry138W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (941 / 2000) (270210813623054157 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry138W_hz2 hx hc) (lowGeometry138W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (941 / 2000) (36887868245552321 / 62500000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry138W_hz33 hx hc) (lowGeometry138W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (941 / 2000) (36887868245552321 / 62500000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry138W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry138W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (464418075849545753 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry138W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (842516207717947 / 976562500000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry138W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (405917568748845121 / 1000000000000000000) (471 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry138W_hz2 hx hc) (lowGeometry138W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (356133304066116299 / 1000000000000000000) (471 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry138W_hz38 hx hc) (lowGeometry138W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (356133304066116299 / 1000000000000000000) (471 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry138W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry138W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (529 / 1000) (1059 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (19827513 / 62500000) (670650983 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (59975377 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry138W_hz12 hx hc).2
  have hrp := (lowGeometry138W_hz16 hx hc).2
  have hbn := (lowGeometry138W_hz21 hx hc).2
  have hlo := (lowGeometry138W_hz40 hx hc).1
  have hhi := (lowGeometry138W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry138C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (529 / 1000) (1059 / 2000) θ := hc

theorem lowGeometry138C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry138C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (941 / 2000) (471 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry138C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (497789 / 2000000) (498789 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry138C_hz0 hx hc) (lowGeometry138C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (498789 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry138C_hz3 hx hc) (lowGeometry138C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (5583396143925309 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry138C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1608018089450489 / 50000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry138C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (529 / 500) (1059 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry138C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry138C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry138C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (8272113644083053 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry138C_hz7 hx hc) (lowGeometry138C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (8156102045667749 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry138C_hz6 hx hc) (lowGeometry138C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (8156102045667749 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry138C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry138C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (413149 / 50000) (827079 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry138C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (827079 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry138C_hz13 hx hc) (lowGeometry138C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (8285333139417749 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry138C_hz12 hx hc) (lowGeometry138C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (8285333139417749 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry138C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry138C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1059 / 16000000) (θ * x) := bmul (lowGeometry138C_hz0 hx hc) (lowGeometry138C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (140674814027631 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry138C_hz17 hx hc) (lowGeometry138C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (11860641383484749 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry138C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (17079323592218039 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry138C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (17079323592218039 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry138C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry138C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (172983 / 100000) (346293 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry138C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry138C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (1209897950206773 / 62500000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry138C_hz22 hx hc) (lowGeometry138C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry138C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry138C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry138C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry138C_hz26 hx hc) (lowGeometry138C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry138C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 0 (19972380281818547 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry138C_hz24 hx hc) (lowGeometry138C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (517079323592218039 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry138C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B 1 (1069484107546342939 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry138C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (941 / 2000) (20149080586173101 / 40000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry138C_hz2 hx hc) (lowGeometry138C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (941 / 2000) (65462424367018259 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry138C_hz33 hx hc) (lowGeometry138C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (941 / 2000) (65462424367018259 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry138C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry138C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (482920676407781961 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry138C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (466424759404299313 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry138C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (438905698599445653 / 1000000000000000000) (471 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry138C_hz2 hx hc) (lowGeometry138C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (209466659158813553 / 500000000000000000) (471 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry138C_hz38 hx hc) (lowGeometry138C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry138C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (529 / 1000) (1059 / 2000) θ) : B (209466659158813553 / 500000000000000000) (471 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry138C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry138C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (529 / 1000) (1059 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (392891427 / 1000000000) (560255397 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65248817 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry138C_hz12 hx hc).2
  have hrp := (lowGeometry138C_hz16 hx hc).2
  have hbn := (lowGeometry138C_hz21 hx hc).2
  have hlo := (lowGeometry138C_hz40 hx hc).1
  have hhi := (lowGeometry138C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry139W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (1059 / 2000) (53 / 100) θ := hc

theorem lowGeometry139W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry139W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (47 / 100) (941 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry139W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (49773 / 200000) (49873 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry139W_hz0 hx hc) (lowGeometry139W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (49873 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry139W_hz3 hx hc) (lowGeometry139W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (1395766478498463 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry139W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (4187299435495389 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry139W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (1059 / 1000) (53 / 50) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry139W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry139W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry139W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (53 / 1000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry139W_hz7 hx hc) (lowGeometry139W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (7499799435495389 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry139W_hz6 hx hc) (lowGeometry139W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (7499799435495389 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry139W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry139W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (1059 / 50) (106 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry139W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (53 / 20000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry139W_hz13 hx hc) (lowGeometry139W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (7665424435495389 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry139W_hz12 hx hc) (lowGeometry139W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (7665424435495389 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry139W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry139W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (53 / 800000) (θ * x) := bmul (lowGeometry139W_hz0 hx hc) (lowGeometry139W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (140957446808511 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry139W_hz17 hx hc) (lowGeometry139W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (2968137534807297 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry139W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (8904412604421891 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry139W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (8904412604421891 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry139W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry139W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (1059 / 250) (106 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry139W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry139W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (5925580140374443 / 125000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry139W_hz22 hx hc) (lowGeometry139W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry139W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry139W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry139W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry139W_hz26 hx hc) (lowGeometry139W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry139W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (9966255063964599 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry139W_hz24 hx hc) (lowGeometry139W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (133904412604421891 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry139W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (1147545069755856653 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry139W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (47 / 100) (134979988830032639 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry139W_hz2 hx hc) (lowGeometry139W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (47 / 100) (589751230639953551 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry139W_hz33 hx hc) (lowGeometry139W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (47 / 100) (589751230639953551 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry139W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry139W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (116095587395578109 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry139W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (43130193320717807 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry139W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (81084763442949477 / 200000000000000000) (941 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry139W_hz2 hx hc) (lowGeometry139W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (35559254189492439 / 100000000000000000) (941 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry139W_hz38 hx hc) (lowGeometry139W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (35559254189492439 / 100000000000000000) (941 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry139W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry139W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1059 / 2000) (53 / 100) θ) :
    OverlapGuard n θ lowWideWindow (316744807 / 1000000000) (67016941 / 100000000) ∧ radiusMinus n θ lowWideWindow ≤ (119996791 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry139W_hz12 hx hc).2
  have hrp := (lowGeometry139W_hz16 hx hc).2
  have hbn := (lowGeometry139W_hz21 hx hc).2
  have hlo := (lowGeometry139W_hz40 hx hc).1
  have hhi := (lowGeometry139W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry139C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (1059 / 2000) (53 / 100) θ := hc

theorem lowGeometry139C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry139C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (47 / 100) (941 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry139C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (49773 / 200000) (49873 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry139C_hz0 hx hc) (lowGeometry139C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (49873 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry139C_hz3 hx hc) (lowGeometry139C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (1395766478498463 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry139C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (8039614916151147 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry139C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (1059 / 1000) (53 / 50) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry139C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry139C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry139C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (8279924893983037 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry139C_hz7 hx hc) (lowGeometry139C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (2039942476266773 / 31250000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry139C_hz6 hx hc) (lowGeometry139C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (2039942476266773 / 31250000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry139C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry139C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (827079 / 100000) (41393 / 5000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry139C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (41393 / 40000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry139C_hz13 hx hc) (lowGeometry139C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (2072280757516773 / 31250000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry139C_hz12 hx hc) (lowGeometry139C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (2072280757516773 / 31250000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry139C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry139C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (53 / 800000) (θ * x) := bmul (lowGeometry139C_hz0 hx hc) (lowGeometry139C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (140957446808511 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry139C_hz17 hx hc) (lowGeometry139C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (2968137534807297 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry139C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (17096472200490031 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry139C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (17096472200490031 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry139C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry139C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (346293 / 200000) (17331 / 10000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry139C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry139C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (19376647059024429 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry139C_hz22 hx hc) (lowGeometry139C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry139C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry139C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry139C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry139C_hz26 hx hc) (lowGeometry139C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry139C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 0 (9995619971070661 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry139C_hz24 hx hc) (lowGeometry139C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (517096472200490031 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry139C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B 1 (534777523124384319 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry139C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (47 / 100) (100645129852009129 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry139C_hz2 hx hc) (lowGeometry139C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (47 / 100) (523216889202186967 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry139C_hz33 hx hc) (lowGeometry139C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (47 / 100) (523216889202186967 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry139C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry139C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (482903527799509969 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry139C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (932783268644848389 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry139C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (219204068131539371 / 500000000000000000) (941 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry139C_hz2 hx hc) (lowGeometry139C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (20920844816046871 / 50000000000000000) (941 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry139C_hz38 hx hc) (lowGeometry139C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry139C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1059 / 2000) (53 / 100) θ) : B (20920844816046871 / 50000000000000000) (941 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry139C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry139C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1059 / 2000) (53 / 100) θ) :
    OverlapGuard n θ lowCoreWindow (392395949 / 1000000000) (279878391 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (815977 / 12500000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry139C_hz12 hx hc).2
  have hrp := (lowGeometry139C_hz16 hx hc).2
  have hbn := (lowGeometry139C_hz21 hx hc).2
  have hlo := (lowGeometry139C_hz40 hx hc).1
  have hhi := (lowGeometry139C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry140W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (53 / 100) (1061 / 2000) θ := hc

theorem lowGeometry140W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry140W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (939 / 2000) (47 / 100) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (49767 / 200000) (49867 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry140W_hz0 hx hc) (lowGeometry140W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (49867 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry140W_hz3 hx hc) (lowGeometry140W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1395682516727927 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry140W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (4187047550183781 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry140W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (53 / 50) (1061 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry140W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry140W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry140W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1061 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry140W_hz7 hx hc) (lowGeometry140W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (7502672550183781 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry140W_hz6 hx hc) (lowGeometry140W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (7502672550183781 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry140W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry140W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (106 / 5) (1061 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry140W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1061 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry140W_hz13 hx hc) (lowGeometry140W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (7668453800183781 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry140W_hz12 hx hc) (lowGeometry140W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (7668453800183781 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry140W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry140W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1061 / 16000000) (θ * x) := bmul (lowGeometry140W_hz0 hx hc) (lowGeometry140W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (28248136315229 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry140W_hz17 hx hc) (lowGeometry140W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (5942236144250433 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry140W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (17826708432751299 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry140W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (17826708432751299 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry140W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry140W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (106 / 25) (1061 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry140W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry140W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (2372468124127277 / 50000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry140W_hz22 hx hc) (lowGeometry140W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry140W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry140W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry140W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry140W_hz26 hx hc) (lowGeometry140W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry140W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (3117392872307323 / 62500000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry140W_hz24 hx hc) (lowGeometry140W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (267826708432751299 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry140W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (1147698331998751613 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry140W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (939 / 2000) (539418216039413259 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry140W_hz2 hx hc) (lowGeometry140W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (939 / 2000) (589296501996330427 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry140W_hz33 hx hc) (lowGeometry140W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (939 / 2000) (589296501996330427 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry140W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry140W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (232173291567248701 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry140W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (215617749268682707 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry140W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (404930133126586123 / 1000000000000000000) (47 / 100) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry140W_hz2 hx hc) (lowGeometry140W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (71010369433933791 / 200000000000000000) (47 / 100) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry140W_hz38 hx hc) (lowGeometry140W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (71010369433933791 / 200000000000000000) (47 / 100) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry140W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry140W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (53 / 100) (1061 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (39531191 / 125000000) (334843829 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (120042761 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry140W_hz12 hx hc).2
  have hrp := (lowGeometry140W_hz16 hx hc).2
  have hbn := (lowGeometry140W_hz21 hx hc).2
  have hlo := (lowGeometry140W_hz40 hx hc).1
  have hhi := (lowGeometry140W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry140C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (53 / 100) (1061 / 2000) θ := hc

theorem lowGeometry140C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry140C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (939 / 2000) (47 / 100) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (49767 / 200000) (49867 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry140C_hz0 hx hc) (lowGeometry140C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (49867 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry140C_hz3 hx hc) (lowGeometry140C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1395682516727927 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry140C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (32156525185411439 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry140C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (53 / 50) (1061 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry140C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry140C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry140C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (8287736143883021 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry140C_hz7 hx hc) (lowGeometry140C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (65307469760943523 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry140C_hz6 hx hc) (lowGeometry140C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (65307469760943523 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry140C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry140C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (41393 / 5000) (828641 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry140C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (828641 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry140C_hz13 hx hc) (lowGeometry140C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (66343271010943523 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry140C_hz12 hx hc) (lowGeometry140C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (66343271010943523 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry140C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry140C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1061 / 16000000) (θ * x) := bmul (lowGeometry140C_hz0 hx hc) (lowGeometry140C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (28248136315229 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry140C_hz17 hx hc) (lowGeometry140C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (5942236144250433 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry140C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (6845456038176499 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry140C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (6845456038176499 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry140C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry140C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (17331 / 10000) (346947 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry140C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry140C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (1939492691474049 / 100000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry140C_hz22 hx hc) (lowGeometry140C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry140C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry140C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry140C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry140C_hz26 hx hc) (lowGeometry140C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry140C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 0 (20010099602464097 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry140C_hz24 hx hc) (lowGeometry140C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (206845456038176499 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry140C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B 1 (133703258386378771 / 125000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry140C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (939 / 2000) (502724251532784179 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry140C_hz2 hx hc) (lowGeometry140C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (939 / 2000) (130683587783812069 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry140C_hz33 hx hc) (lowGeometry140C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (939 / 2000) (130683587783812069 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry140C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry140C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (193154543961823501 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry140C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (932716946327500187 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry140C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (437910606300761337 / 1000000000000000000) (47 / 100) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry140C_hz2 hx hc) (lowGeometry140C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (10447512667457431 / 25000000000000000) (47 / 100) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry140C_hz38 hx hc) (lowGeometry140C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry140C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (1061 / 2000) θ) : B (10447512667457431 / 25000000000000000) (47 / 100) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry140C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry140C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (53 / 100) (1061 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (195950271 / 500000000) (279629041 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (6530747 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry140C_hz12 hx hc).2
  have hrp := (lowGeometry140C_hz16 hx hc).2
  have hbn := (lowGeometry140C_hz21 hx hc).2
  have hlo := (lowGeometry140C_hz40 hx hc).1
  have hhi := (lowGeometry140C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry141W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (1061 / 2000) (531 / 1000) θ := hc

theorem lowGeometry141W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry141W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (469 / 1000) (939 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry141W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (497609 / 2000000) (498609 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry141W_hz0 hx hc) (lowGeometry141W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (498609 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry141W_hz3 hx hc) (lowGeometry141W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (2791194300832531 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry141W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (8373582902497593 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry141W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (1061 / 1000) (531 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry141W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry141W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry141W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (531 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry141W_hz7 hx hc) (lowGeometry141W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (15011082902497593 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry141W_hz6 hx hc) (lowGeometry141W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (15011082902497593 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry141W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry141W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (1061 / 50) (531 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry141W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (531 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry141W_hz13 hx hc) (lowGeometry141W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (15342957902497593 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry141W_hz12 hx hc) (lowGeometry141W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (15342957902497593 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry141W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry141W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (531 / 8000000) (θ * x) := bmul (lowGeometry141W_hz0 hx hc) (lowGeometry141W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (17690565031983 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry141W_hz17 hx hc) (lowGeometry141W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (5948203935976473 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry141W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (17844611807929419 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry141W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (17844611807929419 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry141W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry141W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (1061 / 250) (531 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry141W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry141W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (2968380240130971 / 62500000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry141W_hz22 hx hc) (lowGeometry141W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry141W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry141W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry141W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry141W_hz26 hx hc) (lowGeometry141W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry141W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (2496264829700567 / 50000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry141W_hz24 hx hc) (lowGeometry141W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (267844611807929419 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry141W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (1147851777192646457 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry141W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (469 / 1000) (67364551173993439 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry141W_hz2 hx hc) (lowGeometry141W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (469 / 1000) (147210426496489713 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry141W_hz33 hx hc) (lowGeometry141W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (469 / 1000) (147210426496489713 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry141W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry141W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (232155388192070581 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry141W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (107792248533221969 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry141W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (404436516496648827 / 1000000000000000000) (939 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry141W_hz2 hx hc) (lowGeometry141W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (354511219902637487 / 1000000000000000000) (939 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry141W_hz38 hx hc) (lowGeometry141W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (354511219902637487 / 1000000000000000000) (939 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry141W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry141W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1061 / 2000) (531 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (315754371 / 1000000000) (20912679 / 31250000) ∧ radiusMinus n θ lowWideWindow ≤ (15011083 / 125000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry141W_hz12 hx hc).2
  have hrp := (lowGeometry141W_hz16 hx hc).2
  have hbn := (lowGeometry141W_hz21 hx hc).2
  have hlo := (lowGeometry141W_hz40 hx hc).1
  have hhi := (lowGeometry141W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry141C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (1061 / 2000) (531 / 1000) θ := hc

theorem lowGeometry141C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry141C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (469 / 1000) (939 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry141C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (497609 / 2000000) (498609 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry141C_hz0 hx hc) (lowGeometry141C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (498609 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry141C_hz3 hx hc) (lowGeometry141C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (2791194300832531 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry141C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (16077279172795379 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry141C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (1061 / 1000) (531 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry141C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry141C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry141C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (1659109478756601 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry141C_hz7 hx hc) (lowGeometry141C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (32668373960361389 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry141C_hz6 hx hc) (lowGeometry141C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (32668373960361389 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry141C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry141C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (828641 / 100000) (414711 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry141C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (414711 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry141C_hz13 hx hc) (lowGeometry141C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (33186762710361389 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry141C_hz12 hx hc) (lowGeometry141C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (33186762710361389 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry141C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry141C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (531 / 8000000) (θ * x) := bmul (lowGeometry141C_hz0 hx hc) (lowGeometry141C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (17690565031983 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry141C_hz17 hx hc) (lowGeometry141C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (5948203935976473 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry141C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (6852330934244897 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry141C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (6852330934244897 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry141C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry141C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (346947 / 200000) (173637 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry141C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry141C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (19413206770456551 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry141C_hz22 hx hc) (lowGeometry141C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry141C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry141C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry141C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry141C_hz26 hx hc) (lowGeometry141C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry141C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 0 (2503619907848359 / 125000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry141C_hz24 hx hc) (lowGeometry141C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (206852330934244897 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry141C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B 1 (1069697170323259209 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry141C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (469 / 1000) (502222821466770199 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry141C_hz2 hx hc) (lowGeometry141C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (469 / 1000) (522251780729557071 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry141C_hz33 hx hc) (lowGeometry141C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (469 / 1000) (522251780729557071 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry141C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry141C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (193147669065755103 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry141C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (233162637909590317 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry141C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (218706554359195717 / 500000000000000000) (939 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry141C_hz2 hx hc) (lowGeometry141C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (208692074727802281 / 500000000000000000) (939 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry141C_hz38 hx hc) (lowGeometry141C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry141C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1061 / 2000) (531 / 1000) θ) : B (208692074727802281 / 500000000000000000) (939 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry141C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry141C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1061 / 2000) (531 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (195702603 / 500000000) (558759297 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (16334187 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry141C_hz12 hx hc).2
  have hrp := (lowGeometry141C_hz16 hx hc).2
  have hbn := (lowGeometry141C_hz21 hx hc).2
  have hlo := (lowGeometry141C_hz40 hx hc).1
  have hhi := (lowGeometry141C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry142W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (531 / 1000) (1063 / 2000) θ := hc

theorem lowGeometry142W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry142W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (937 / 2000) (469 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry142W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (497547 / 2000000) (498547 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry142W_hz0 hx hc) (lowGeometry142W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (498547 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry142W_hz3 hx hc) (lowGeometry142W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (697755189652861 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry142W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (2093265568958583 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry142W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (531 / 500) (1063 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry142W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry142W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry142W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1063 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry142W_hz7 hx hc) (lowGeometry142W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (3754203068958583 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry142W_hz6 hx hc) (lowGeometry142W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (3754203068958583 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry142W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry142W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (531 / 25) (1063 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry142W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1063 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry142W_hz13 hx hc) (lowGeometry142W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (3837249943958583 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry142W_hz12 hx hc) (lowGeometry142W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (3837249943958583 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry142W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry142W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1063 / 16000000) (θ * x) := bmul (lowGeometry142W_hz0 hx hc) (lowGeometry142W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (141808964781217 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry142W_hz17 hx hc) (lowGeometry142W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (5954178465187641 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry142W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (17862535395562923 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry142W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (17862535395562923 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry142W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry142W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (531 / 125) (1063 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry142W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry142W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (11884701300411383 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry142W_hz22 hx hc) (lowGeometry142W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry142W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry142W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry142W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry142W_hz26 hx hc) (lowGeometry142W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry142W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (49972307231105513 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry142W_hz24 hx hc) (lowGeometry142W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (267862535395562923 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry142W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (1148005405896627197 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry142W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (937 / 2000) (134603633841379539 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry142W_hz2 hx hc) (lowGeometry142W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (937 / 2000) (588386842596623669 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry142W_hz33 hx hc) (lowGeometry142W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (937 / 2000) (588386842596623669 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry142W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry142W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (232137464604437077 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry142W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (215551209891905107 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry142W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (40394296733743017 / 100000000000000000) (469 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry142W_hz2 hx hc) (lowGeometry142W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (353970660106324657 / 1000000000000000000) (469 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry142W_hz38 hx hc) (lowGeometry142W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (353970660106324657 / 1000000000000000000) (469 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry142W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry142W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (531 / 1000) (1063 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (39407417 / 125000000) (33436181 / 50000000) ∧ radiusMinus n θ lowWideWindow ≤ (120134499 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry142W_hz12 hx hc).2
  have hrp := (lowGeometry142W_hz16 hx hc).2
  have hbn := (lowGeometry142W_hz21 hx hc).2
  have hlo := (lowGeometry142W_hz40 hx hc).1
  have hhi := (lowGeometry142W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry142C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (531 / 1000) (1063 / 2000) θ := hc

theorem lowGeometry142C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry142C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (937 / 2000) (469 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry142C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (497547 / 2000000) (498547 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry142C_hz0 hx hc) (lowGeometry142C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (498547 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry142C_hz3 hx hc) (lowGeometry142C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (697755189652861 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry142C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (6430511827840767 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry142C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (531 / 500) (1063 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry142C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry142C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry142C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (8303358643682989 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry142C_hz7 hx hc) (lowGeometry142C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (65365993713935791 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry142C_hz6 hx hc) (lowGeometry142C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (65365993713935791 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry142C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry142C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (414711 / 50000) (830203 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry142C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (830203 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry142C_hz13 hx hc) (lowGeometry142C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (66403747463935791 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry142C_hz12 hx hc) (lowGeometry142C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (66403747463935791 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry142C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry142C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (1063 / 16000000) (θ * x) := bmul (lowGeometry142C_hz0 hx hc) (lowGeometry142C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (141808964781217 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry142C_hz17 hx hc) (lowGeometry142C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (5954178465187641 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry142C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (34296067959480813 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry142C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (34296067959480813 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry142C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry142C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (173637 / 100000) (347601 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry142C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry142C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (19431486626172611 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry142C_hz22 hx hc) (lowGeometry142C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry142C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry142C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry142C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry142C_hz26 hx hc) (lowGeometry142C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry142C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 0 (10023909461554823 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry142C_hz24 hx hc) (lowGeometry142C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (1034296067959480813 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry142C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B 1 (1069768356196442953 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry142C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (937 / 2000) (100344271811226349 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry142C_hz2 hx hc) (lowGeometry142C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (937 / 2000) (521769177979241391 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry142C_hz33 hx hc) (lowGeometry142C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (937 / 2000) (521769177979241391 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry142C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry142C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (965703932040519187 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry142C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (9325840843585197 / 10000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry142C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (436915643521966479 / 1000000000000000000) (469 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry142C_hz2 hx hc) (lowGeometry142C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (416867824598856833 / 1000000000000000000) (469 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry142C_hz38 hx hc) (lowGeometry142C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry142C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (531 / 1000) (1063 / 2000) θ) : B (416867824598856833 / 1000000000000000000) (469 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry142C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry142C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (531 / 1000) (1063 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (390909939 / 1000000000) (279130213 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32682997 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry142C_hz12 hx hc).2
  have hrp := (lowGeometry142C_hz16 hx hc).2
  have hbn := (lowGeometry142C_hz21 hx hc).2
  have hlo := (lowGeometry142C_hz40 hx hc).1
  have hhi := (lowGeometry142C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry143W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (1063 / 2000) (133 / 250) θ := hc

theorem lowGeometry143W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry143W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (117 / 250) (937 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry143W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (124371 / 500000) (124621 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry143W_hz0 hx hc) (lowGeometry143W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (124621 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry143W_hz3 hx hc) (lowGeometry143W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (5581688812536937 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry143W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (16745066437610811 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry143W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (1063 / 1000) (133 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry143W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry143W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry143W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (133 / 2500) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry143W_hz7 hx hc) (lowGeometry143W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (30045066437610811 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry143W_hz6 hx hc) (lowGeometry143W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (30045066437610811 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry143W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry143W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (1063 / 50) (532 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry143W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (133 / 50000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry143W_hz13 hx hc) (lowGeometry143W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (30710066437610811 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry143W_hz12 hx hc) (lowGeometry143W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (30710066437610811 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry143W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry143W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (133 / 2000000) (θ * x) := bmul (lowGeometry143W_hz0 hx hc) (lowGeometry143W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (71047008547009 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry143W_hz17 hx hc) (lowGeometry143W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (47681278018781 / 4000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry143W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (143043834056343 / 2000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry143W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (143043834056343 / 2000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry143W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry143W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (1063 / 250) (532 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry143W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry143W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (47583526561195527 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry143W_hz22 hx hc) (lowGeometry143W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry143W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry143W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry143W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry143W_hz26 hx hc) (lowGeometry143W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry143W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (10003863573639937 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry143W_hz24 hx hc) (lowGeometry143W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (2143043834056343 / 2000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry143W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (1148159218671727649 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry143W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (117 / 250) (134478148486926101 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry143W_hz2 hx hc) (lowGeometry143W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (117 / 250) (587931911815904089 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry143W_hz33 hx hc) (lowGeometry143W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (117 / 250) (587931911815904089 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry143W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry143W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (1856956165943657 / 2000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry143W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (53879471909940103 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry143W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (403449485661631491 / 1000000000000000000) (937 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry143W_hz2 hx hc) (lowGeometry143W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (176715083896715903 / 500000000000000000) (937 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry143W_hz38 hx hc) (lowGeometry143W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (176715083896715903 / 500000000000000000) (937 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry143W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry143W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1063 / 2000) (133 / 250) θ) :
    OverlapGuard n θ lowWideWindow (157382211 / 500000000) (668241333 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (60090133 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry143W_hz12 hx hc).2
  have hrp := (lowGeometry143W_hz16 hx hc).2
  have hbn := (lowGeometry143W_hz21 hx hc).2
  have hlo := (lowGeometry143W_hz40 hx hc).1
  have hhi := (lowGeometry143W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry143C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (1063 / 2000) (133 / 250) θ := hc

theorem lowGeometry143C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry143C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (117 / 250) (937 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry143C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (124371 / 500000) (124621 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry143C_hz0 hx hc) (lowGeometry143C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (124621 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry143C_hz3 hx hc) (lowGeometry143C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (5581688812536937 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry143C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (16075263780106379 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry143C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (1063 / 1000) (133 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry143C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry143C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry143C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (8311169893582973 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry143C_hz7 hx hc) (lowGeometry143C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1307904142690893 / 20000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry143C_hz6 hx hc) (lowGeometry143C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1307904142690893 / 20000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry143C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry143C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (830203 / 100000) (103873 / 12500) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry143C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (103873 / 100000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry143C_hz13 hx hc) (lowGeometry143C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1328678742690893 / 20000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry143C_hz12 hx hc) (lowGeometry143C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (1328678742690893 / 20000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry143C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry143C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (133 / 2000000) (θ * x) := bmul (lowGeometry143C_hz0 hx hc) (lowGeometry143C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (71047008547009 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry143C_hz17 hx hc) (lowGeometry143C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (47681278018781 / 4000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry143C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (429131502169029 / 12500000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry143C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (429131502169029 / 12500000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry143C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry143C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (347601 / 200000) (43491 / 25000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry143C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry143C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (607805202559021 / 31250000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry143C_hz22 hx hc) (lowGeometry143C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry143C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry143C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry143C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry143C_hz26 hx hc) (lowGeometry143C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry143C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 0 (20066678583432421 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry143C_hz24 hx hc) (lowGeometry143C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (12929131502169029 / 12500000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry143C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B 1 (1069839624962429263 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry143C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (117 / 250) (50121986429489811 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry143C_hz2 hx hc) (lowGeometry143C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (117 / 250) (521286542878330531 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry143C_hz33 hx hc) (lowGeometry143C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (117 / 250) (521286542878330531 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry143C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry143C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (12070868497830971 / 12500000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry143C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (466258772134169991 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry143C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (436418210717583111 / 1000000000000000000) (937 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry143C_hz2 hx hc) (lowGeometry143C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (41635153213415069 / 100000000000000000) (937 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry143C_hz38 hx hc) (lowGeometry143C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry143C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1063 / 2000) (133 / 250) θ) : B (41635153213415069 / 100000000000000000) (937 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry143C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry143C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1063 / 2000) (133 / 250) θ) :
    OverlapGuard n θ lowCoreWindow (390414743 / 1000000000) (55776147 / 100000000) ∧ radiusMinus n θ lowCoreWindow ≤ (8174401 / 125000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry143C_hz12 hx hc).2
  have hrp := (lowGeometry143C_hz16 hx hc).2
  have hbn := (lowGeometry143C_hz21 hx hc).2
  have hlo := (lowGeometry143C_hz40 hx hc).1
  have hhi := (lowGeometry143C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry144W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (133 / 250) (213 / 400) θ := hc

theorem lowGeometry144W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry144W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (187 / 400) (117 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry144W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (24871 / 100000) (24921 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry144W_hz0 hx hc) (lowGeometry144W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (24921 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry144W_hz3 hx hc) (lowGeometry144W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (2790665243270859 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry144W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (8371995729812577 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry144W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (133 / 125) (213 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry144W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry144W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry144W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (213 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry144W_hz7 hx hc) (lowGeometry144W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (15028245729812577 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry144W_hz6 hx hc) (lowGeometry144W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (15028245729812577 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry144W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry144W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (532 / 25) (213 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry144W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (213 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry144W_hz13 hx hc) (lowGeometry144W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (15361058229812577 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry144W_hz12 hx hc) (lowGeometry144W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (15361058229812577 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry144W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry144W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (213 / 3200000) (θ * x) := bmul (lowGeometry144W_hz0 hx hc) (lowGeometry144W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (71189839572193 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry144W_hz17 hx hc) (lowGeometry144W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (2983073908994567 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry144W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (8949221726983701 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry144W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (8949221726983701 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry144W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry144W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (532 / 125) (213 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry144W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry144W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (47628247920745523 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry144W_hz22 hx hc) (lowGeometry144W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry144W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry144W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry144W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry144W_hz26 hx hc) (lowGeometry144W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry144W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (25033164252646929 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry144W_hz24 hx hc) (lowGeometry144W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (133949221726983701 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry144W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (1148313216080937113 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry144W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (187 / 400) (537410585125878569 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry144W_hz2 hx hc) (lowGeometry144W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (187 / 400) (587476913631172427 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry144W_hz33 hx hc) (lowGeometry144W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (187 / 400) (587476913631172427 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry144W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry144W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (116050778273016299 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry144W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (21548453020436467 / 25000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry144W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (100739017870540483 / 250000000000000000) (117 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry144W_hz2 hx hc) (lowGeometry144W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (176444871488434037 / 500000000000000000) (117 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry144W_hz38 hx hc) (lowGeometry144W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (176444871488434037 / 500000000000000000) (117 / 250) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry144W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry144W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (133 / 250) (213 / 400) θ) :
    OverlapGuard n θ lowWideWindow (31426963 / 100000000) (667758869 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (60112983 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry144W_hz12 hx hc).2
  have hrp := (lowGeometry144W_hz16 hx hc).2
  have hbn := (lowGeometry144W_hz21 hx hc).2
  have hlo := (lowGeometry144W_hz40 hx hc).1
  have hhi := (lowGeometry144W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry144C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (133 / 250) (213 / 400) θ := hc

theorem lowGeometry144C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry144C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (187 / 400) (117 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry144C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (24871 / 100000) (24921 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry144C_hz0 hx hc) (lowGeometry144C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (24921 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry144C_hz3 hx hc) (lowGeometry144C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (2790665243270859 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry144C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (4018557950310037 / 125000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry144C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (133 / 125) (213 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry144C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry144C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry144C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (8318981143482957 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry144C_hz7 hx hc) (lowGeometry144C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (16356097044103031 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry144C_hz6 hx hc) (lowGeometry144C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (16356097044103031 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry144C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry144C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (103873 / 12500) (166353 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry144C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (166353 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry144C_hz13 hx hc) (lowGeometry144C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (16616023606603031 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry144C_hz12 hx hc) (lowGeometry144C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (16616023606603031 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry144C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry144C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (213 / 3200000) (θ * x) := bmul (lowGeometry144C_hz0 hx hc) (lowGeometry144C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (71189839572193 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry144C_hz17 hx hc) (lowGeometry144C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (2983073908994567 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry144C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (8591252857904353 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry144C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (8591252857904353 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry144C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry144C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (43491 / 25000) (69651 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry144C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry144C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (19468046337604733 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry144C_hz22 hx hc) (lowGeometry144C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry144C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry144C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry144C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry144C_hz26 hx hc) (lowGeometry144C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry144C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 0 (5021384560938799 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry144C_hz24 hx hc) (lowGeometry144C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (258591252857904353 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry144C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B 1 (53495548843696501 / 50000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry144C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (187 / 400) (2002873348707997 / 4000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry144C_hz2 hx hc) (lowGeometry144C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (187 / 400) (260401937710377223 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry144C_hz33 hx hc) (lowGeometry144C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (187 / 400) (260401937710377223 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry144C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry144C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (241408747142095647 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry144C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (932450931147460371 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry144C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (435920810311437723 / 1000000000000000000) (117 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry144C_hz2 hx hc) (lowGeometry144C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (415835272067682527 / 1000000000000000000) (117 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry144C_hz38 hx hc) (lowGeometry144C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry144C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (133 / 250) (213 / 400) θ) : B (415835272067682527 / 1000000000000000000) (117 / 250) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry144C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry144C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (133 / 250) (213 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (389919617 / 1000000000) (557262429 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65424389 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry144C_hz12 hx hc).2
  have hrp := (lowGeometry144C_hz16 hx hc).2
  have hbn := (lowGeometry144C_hz21 hx hc).2
  have hlo := (lowGeometry144C_hz40 hx hc).1
  have hhi := (lowGeometry144C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry145W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (213 / 400) (533 / 1000) θ := hc

theorem lowGeometry145W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry145W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (467 / 1000) (187 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry145W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (99471 / 400000) (99671 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry145W_hz0 hx hc) (lowGeometry145W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (99671 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry145W_hz3 hx hc) (lowGeometry145W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (69762081726931 / 12500000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry145W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (209286245180793 / 3125000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry145W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (213 / 200) (533 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry145W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry145W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry145W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (533 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry145W_hz7 hx hc) (lowGeometry145W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (375848745180793 / 3125000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry145W_hz6 hx hc) (lowGeometry145W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (375848745180793 / 3125000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry145W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry145W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (213 / 10) (533 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry145W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (533 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry145W_hz13 hx hc) (lowGeometry145W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (384176870180793 / 3125000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry145W_hz12 hx hc) (lowGeometry145W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (384176870180793 / 3125000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry145W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry145W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (533 / 8000000) (θ * x) := bmul (lowGeometry145W_hz0 hx hc) (lowGeometry145W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (142665952890793 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry145W_hz17 hx hc) (lowGeometry145W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (238885707308573 / 20000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry145W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (716657121925719 / 10000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry145W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (716657121925719 / 10000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry145W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry145W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (213 / 50) (533 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry145W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry145W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (47672969280295519 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry145W_hz22 hx hc) (lowGeometry145W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry145W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry145W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry145W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry145W_hz26 hx hc) (lowGeometry145W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry145W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (50113339142388031 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry145W_hz24 hx hc) (lowGeometry145W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (10716657121925719 / 10000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry145W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (1148467398689212349 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry145W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (467 / 1000) (268454254443603387 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry145W_hz2 hx hc) (lowGeometry145W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (467 / 1000) (117404369605918961 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry145W_hz33 hx hc) (lowGeometry145W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (467 / 1000) (117404369605918961 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry145W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry145W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (9283342878074281 / 10000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry145W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (215451137479731187 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry145W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (402462724812137857 / 1000000000000000000) (187 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry145W_hz2 hx hc) (lowGeometry145W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (176174692834874913 / 500000000000000000) (187 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry145W_hz38 hx hc) (lowGeometry145W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (176174692834874913 / 500000000000000000) (187 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry145W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry145W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (213 / 400) (533 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (313774959 / 1000000000) (667276227 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (120271599 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry145W_hz12 hx hc).2
  have hrp := (lowGeometry145W_hz16 hx hc).2
  have hbn := (lowGeometry145W_hz21 hx hc).2
  have hlo := (lowGeometry145W_hz40 hx hc).1
  have hhi := (lowGeometry145W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry145C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (213 / 400) (533 / 1000) θ := hc

theorem lowGeometry145C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry145C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (467 / 1000) (187 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry145C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (99471 / 400000) (99671 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry145C_hz0 hx hc) (lowGeometry145C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (99671 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry145C_hz3 hx hc) (lowGeometry145C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (69762081726931 / 12500000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry145C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (6429273451953961 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry145C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (213 / 200) (533 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry145C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry145C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry145C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (8326792393382941 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry145C_hz7 hx hc) (lowGeometry145C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (65453536833301569 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry145C_hz6 hx hc) (lowGeometry145C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (65453536833301569 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry145C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry145C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (166353 / 20000) (416273 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry145C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (416273 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry145C_hz13 hx hc) (lowGeometry145C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (66494219333301569 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry145C_hz12 hx hc) (lowGeometry145C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (66494219333301569 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry145C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry145C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (533 / 8000000) (θ * x) := bmul (lowGeometry145C_hz0 hx hc) (lowGeometry145C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (142665952890793 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry145C_hz17 hx hc) (lowGeometry145C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (238885707308573 / 20000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry145C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (2149971365777157 / 62500000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry145C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (2149971365777157 / 62500000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry145C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry145C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (69651 / 40000) (174291 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry145C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry145C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (9743163096660397 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry145C_hz22 hx hc) (lowGeometry145C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry145C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry145C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry145C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry145C_hz26 hx hc) (lowGeometry145C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry145C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 0 (20104397904077971 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry145C_hz24 hx hc) (lowGeometry145C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (64649971365777157 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry145C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B 1 (534991206092263209 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry145C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (467 / 1000) (500216777696266101 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry145C_hz2 hx hc) (lowGeometry145C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (467 / 1000) (65040146950043009 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry145C_hz33 hx hc) (lowGeometry145C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (467 / 1000) (65040146950043009 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry145C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry145C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (60350028634222843 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry145C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (932384244774788369 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry145C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (54427930288728271 / 125000000000000000) (187 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry145C_hz2 hx hc) (lowGeometry145C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (415319044405748197 / 1000000000000000000) (187 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry145C_hz38 hx hc) (lowGeometry145C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry145C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (213 / 400) (533 / 1000) θ) : B (415319044405748197 / 1000000000000000000) (187 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry145C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry145C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (213 / 400) (533 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (194712281 / 500000000) (556763303 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65453537 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry145C_hz12 hx hc).2
  have hrp := (lowGeometry145C_hz16 hx hc).2
  have hbn := (lowGeometry145C_hz21 hx hc).2
  have hlo := (lowGeometry145C_hz40 hx hc).1
  have hhi := (lowGeometry145C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry146W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (533 / 1000) (1067 / 2000) θ := hc

theorem lowGeometry146W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry146W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (933 / 2000) (467 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry146W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (497289 / 2000000) (498289 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry146W_hz0 hx hc) (lowGeometry146W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (498289 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry146W_hz3 hx hc) (lowGeometry146W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1395149241568801 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry146W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (4185447724706403 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry146W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (533 / 500) (1067 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry146W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry146W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry146W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1067 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry146W_hz7 hx hc) (lowGeometry146W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (7519822724706403 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry146W_hz6 hx hc) (lowGeometry146W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (7519822724706403 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry146W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry146W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (533 / 25) (1067 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry146W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1067 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry146W_hz13 hx hc) (lowGeometry146W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (7686541474706403 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry146W_hz12 hx hc) (lowGeometry146W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (7686541474706403 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry146W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry146W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1067 / 16000000) (θ * x) := bmul (lowGeometry146W_hz0 hx hc) (lowGeometry146W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (35738210075027 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry146W_hz17 hx hc) (lowGeometry146W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (2989072183597571 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry146W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (8967216550792713 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry146W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (8967216550792713 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry146W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry146W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (533 / 125) (1067 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry146W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry146W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (9543538127969103 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry146W_hz22 hx hc) (lowGeometry146W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry146W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry146W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry146W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry146W_hz26 hx hc) (lowGeometry146W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry146W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (12540087444870551 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry146W_hz24 hx hc) (lowGeometry146W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (133967216550792713 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry146W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (1148621767063487297 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry146W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (933 / 2000) (67050795652331071 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry146W_hz2 hx hc) (lowGeometry146W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (933 / 2000) (146641678749532693 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry146W_hz33 hx hc) (lowGeometry146W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (933 / 2000) (146641678749532693 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry146W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry146W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (116032783449207287 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry146W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (5385442733988253 / 6250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry146W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (401969445664883203 / 1000000000000000000) (467 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry146W_hz2 hx hc) (lowGeometry146W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (351809095885400999 / 1000000000000000000) (467 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry146W_hz38 hx hc) (lowGeometry146W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (351809095885400999 / 1000000000000000000) (467 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry146W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry146W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (533 / 1000) (1067 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (31328041 / 100000000) (666793407 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (30079291 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry146W_hz12 hx hc).2
  have hrp := (lowGeometry146W_hz16 hx hc).2
  have hbn := (lowGeometry146W_hz21 hx hc).2
  have hlo := (lowGeometry146W_hz40 hx hc).1
  have hhi := (lowGeometry146W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry146C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (533 / 1000) (1067 / 2000) θ := hc

theorem lowGeometry146C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry146C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (933 / 2000) (467 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry146C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (497289 / 2000000) (498289 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry146C_hz0 hx hc) (lowGeometry146C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (498289 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry146C_hz3 hx hc) (lowGeometry146C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1395149241568801 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry146C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (4018029815718147 / 125000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry146C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (533 / 500) (1067 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry146C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry146C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry146C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (333384145731317 / 10000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry146C_hz7 hx hc) (lowGeometry146C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (16370663274719219 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry146C_hz6 hx hc) (lowGeometry146C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (16370663274719219 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry146C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry146C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (416273 / 50000) (833327 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry146C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (833327 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry146C_hz13 hx hc) (lowGeometry146C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (16631077962219219 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry146C_hz12 hx hc) (lowGeometry146C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (16631077962219219 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry146C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry146C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (1067 / 16000000) (θ * x) := bmul (lowGeometry146C_hz0 hx hc) (lowGeometry146C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (35738210075027 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry146C_hz17 hx hc) (lowGeometry146C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (2989072183597571 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry146C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (17217055777522009 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry146C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (17217055777522009 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry146C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry146C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (174291 / 100000) (348909 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry146C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry146C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (9752303024518427 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry146C_hz22 hx hc) (lowGeometry146C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry146C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry146C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry146C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry146C_hz26 hx hc) (lowGeometry146C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry146C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 0 (4024651512880149 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry146C_hz24 hx hc) (lowGeometry146C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (517217055777522009 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry146C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B 1 (267513482787168313 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry146C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (933 / 2000) (499715185846430409 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry146C_hz2 hx hc) (lowGeometry146C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (933 / 2000) (259919221705415577 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry146C_hz33 hx hc) (lowGeometry146C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (933 / 2000) (259919221705415577 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry146C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry146C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (482782944222477991 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry146C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (932317484928497179 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry146C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (217463053359571967 / 500000000000000000) (467 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry146C_hz2 hx hc) (lowGeometry146C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (414802849154743189 / 1000000000000000000) (467 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry146C_hz38 hx hc) (lowGeometry146C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry146C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (533 / 1000) (1067 / 2000) θ) : B (414802849154743189 / 1000000000000000000) (467 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry146C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry146C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (533 / 1000) (1067 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (48616197 / 125000000) (139066023 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32741327 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry146C_hz12 hx hc).2
  have hrp := (lowGeometry146C_hz16 hx hc).2
  have hbn := (lowGeometry146C_hz21 hx hc).2
  have hlo := (lowGeometry146C_hz40 hx hc).1
  have hhi := (lowGeometry146C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry147W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (1067 / 2000) (267 / 500) θ := hc

theorem lowGeometry147W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry147W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (233 / 500) (933 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry147W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (248611 / 1000000) (249111 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry147W_hz0 hx hc) (lowGeometry147W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (249111 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry147W_hz3 hx hc) (lowGeometry147W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (2790110884893287 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry147W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (8370332654679861 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry147W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (1067 / 1000) (267 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry147W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry147W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry147W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (267 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry147W_hz7 hx hc) (lowGeometry147W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (15045332654679861 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry147W_hz6 hx hc) (lowGeometry147W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (15045332654679861 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry147W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry147W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (1067 / 50) (534 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry147W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (267 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry147W_hz13 hx hc) (lowGeometry147W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (15379082654679861 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry147W_hz12 hx hc) (lowGeometry147W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (15379082654679861 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry147W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry147W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (267 / 4000000) (θ * x) := bmul (lowGeometry147W_hz0 hx hc) (lowGeometry147W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (3581008583691 / 25000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry147W_hz17 hx hc) (lowGeometry147W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (11968305784347257 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry147W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (35904917353041771 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry147W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (35904917353041771 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry147W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry147W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (1067 / 250) (534 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry147W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry147W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (47762411999395511 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry147W_hz22 hx hc) (lowGeometry147W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry147W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry147W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry147W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry147W_hz26 hx hc) (lowGeometry147W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry147W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (50207360416576377 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry147W_hz24 hx hc) (lowGeometry147W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (535904917353041771 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry147W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (9190210574181457 / 8000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry147W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (233 / 500) (133976038526739053 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry147W_hz2 hx hc) (lowGeometry147W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (233 / 500) (586111514523532589 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry147W_hz33 hx hc) (lowGeometry147W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (233 / 500) (586111514523532589 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry147W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry147W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (464095082646958229 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry147W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (215384245737086989 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry147W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (401476234053930147 / 1000000000000000000) (933 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry147W_hz2 hx hc) (lowGeometry147W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (35126887363735377 / 100000000000000000) (933 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry147W_hz38 hx hc) (lowGeometry147W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (35126887363735377 / 100000000000000000) (933 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry147W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry147W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1067 / 2000) (267 / 500) θ) :
    OverlapGuard n θ lowWideWindow (312785981 / 1000000000) (666310409 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (60181331 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry147W_hz12 hx hc).2
  have hrp := (lowGeometry147W_hz16 hx hc).2
  have hbn := (lowGeometry147W_hz21 hx hc).2
  have hlo := (lowGeometry147W_hz40 hx hc).1
  have hhi := (lowGeometry147W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry147C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (1067 / 2000) (267 / 500) θ := hc

theorem lowGeometry147C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry147C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (233 / 500) (933 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry147C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (248611 / 1000000) (249111 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry147C_hz0 hx hc) (lowGeometry147C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (249111 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry147C_hz3 hx hc) (lowGeometry147C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (2790110884893287 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry147C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (32142077393970667 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry147C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (1067 / 1000) (267 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry147C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry147C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry147C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (8342414893182909 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry147C_hz7 hx hc) (lowGeometry147C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (65511736966702303 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry147C_hz6 hx hc) (lowGeometry147C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (65511736966702303 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry147C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry147C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (833327 / 100000) (208527 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry147C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (208527 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry147C_hz13 hx hc) (lowGeometry147C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (66554371966702303 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry147C_hz12 hx hc) (lowGeometry147C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (66554371966702303 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry147C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry147C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (267 / 4000000) (θ * x) := bmul (lowGeometry147C_hz0 hx hc) (lowGeometry147C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (3581008583691 / 25000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry147C_hz17 hx hc) (lowGeometry147C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (11968305784347257 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry147C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (34468720658920101 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry147C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (34468720658920101 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry147C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry147C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (348909 / 200000) (87309 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry147C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry147C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (3904577180950583 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry147C_hz22 hx hc) (lowGeometry147C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry147C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry147C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry147C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry147C_hz26 hx hc) (lowGeometry147C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry147C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 0 (20142117224723521 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry147C_hz24 hx hc) (lowGeometry147C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (1034468720658920101 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry147C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B 1 (267531383505425717 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry147C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (233 / 500) (124803390405281097 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry147C_hz2 hx hc) (lowGeometry147C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (233 / 500) (519355678845847909 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry147C_hz33 hx hc) (lowGeometry147C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (233 / 500) (519355678845847909 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry147C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry147C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (965531279341079899 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry147C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (932250651386022463 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry147C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (434428803545886467 / 1000000000000000000) (933 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry147C_hz2 hx hc) (lowGeometry147C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (207143343160581473 / 500000000000000000) (933 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry147C_hz38 hx hc) (lowGeometry147C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry147C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1067 / 2000) (267 / 500) θ) : B (207143343160581473 / 500000000000000000) (933 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry147C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry147C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1067 / 2000) (267 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (388434661 / 1000000000) (138941199 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65511737 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry147C_hz12 hx hc).2
  have hrp := (lowGeometry147C_hz16 hx hc).2
  have hbn := (lowGeometry147C_hz21 hx hc).2
  have hlo := (lowGeometry147C_hz40 hx hc).1
  have hhi := (lowGeometry147C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry148W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (267 / 500) (1069 / 2000) θ := hc

theorem lowGeometry148W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry148W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (931 / 2000) (233 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry148W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (248577 / 1000000) (249077 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry148W_hz0 hx hc) (lowGeometry148W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (249077 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry148W_hz3 hx hc) (lowGeometry148W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1394960236888493 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry148W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (4184880710665479 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry148W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (267 / 250) (1069 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry148W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry148W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry148W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1069 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry148W_hz7 hx hc) (lowGeometry148W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (7525505710665479 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry148W_hz6 hx hc) (lowGeometry148W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (7525505710665479 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry148W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry148W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (534 / 25) (1069 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry148W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1069 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry148W_hz13 hx hc) (lowGeometry148W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (7692536960665479 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry148W_hz12 hx hc) (lowGeometry148W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (7692536960665479 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry148W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry148W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1069 / 16000000) (θ * x) := bmul (lowGeometry148W_hz0 hx hc) (lowGeometry148W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (71764232008593 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry148W_hz17 hx hc) (lowGeometry148W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (2396067311384937 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry148W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (7188201934154811 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry148W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (7188201934154811 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry148W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry148W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (534 / 125) (1069 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry148W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry148W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (23903566679472753 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry148W_hz22 hx hc) (lowGeometry148W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry148W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry148W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry148W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry148W_hz26 hx hc) (lowGeometry148W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry148W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (12563592763417637 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry148W_hz24 hx hc) (lowGeometry148W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (107188201934154811 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry148W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (1148931063387714917 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry148W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (931 / 2000) (33462617221167197 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry148W_hz2 hx hc) (lowGeometry148W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (931 / 2000) (5856562465923457 / 10000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry148W_hz33 hx hc) (lowGeometry148W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (931 / 2000) (5856562465923457 / 10000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry148W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry148W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (92811798065845189 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry148W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (215350746505380619 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry148W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (50122886249127339 / 125000000000000000) (233 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry148W_hz2 hx hc) (lowGeometry148W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (87682179734837041 / 250000000000000000) (233 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry148W_hz38 hx hc) (lowGeometry148W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (87682179734837041 / 250000000000000000) (233 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry148W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry148W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (267 / 500) (1069 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (156145837 / 500000000) (665827233 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (30102023 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry148W_hz12 hx hc).2
  have hrp := (lowGeometry148W_hz16 hx hc).2
  have hbn := (lowGeometry148W_hz21 hx hc).2
  have hlo := (lowGeometry148W_hz40 hx hc).1
  have hhi := (lowGeometry148W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry148C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (267 / 500) (1069 / 2000) θ := hc

theorem lowGeometry148C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry148C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (931 / 2000) (233 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry148C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (248577 / 1000000) (249077 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry148C_hz0 hx hc) (lowGeometry148C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (249077 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry148C_hz3 hx hc) (lowGeometry148C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1394960236888493 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry148C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (32139883857910879 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry148C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (267 / 250) (1069 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry148C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry148C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry148C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (8350226143082893 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry148C_hz7 hx hc) (lowGeometry148C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (65540788430242451 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry148C_hz6 hx hc) (lowGeometry148C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (65540788430242451 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry148C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry148C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (208527 / 25000) (834889 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry148C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (834889 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry148C_hz13 hx hc) (lowGeometry148C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (66584399680242451 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry148C_hz12 hx hc) (lowGeometry148C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (66584399680242451 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry148C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry148C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1069 / 16000000) (θ * x) := bmul (lowGeometry148C_hz0 hx hc) (lowGeometry148C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (71764232008593 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry148C_hz17 hx hc) (lowGeometry148C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (2396067311384937 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry148C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (34503369283943093 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry148C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (34503369283943093 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry148C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry148C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (87309 / 50000) (349563 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry148C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry148C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (1221322860029311 / 62500000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry148C_hz22 hx hc) (lowGeometry148C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry148C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry148C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry148C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry148C_hz26 hx hc) (lowGeometry148C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry148C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 0 (2520122110630787 / 125000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry148C_hz24 hx hc) (lowGeometry148C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (1034503369283943093 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry148C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B 1 (535098610529915167 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry148C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (931 / 2000) (62338988126735117 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry148C_hz2 hx hc) (lowGeometry148C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (931 / 2000) (4053694389835369 / 7812500000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry148C_hz33 hx hc) (lowGeometry148C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (931 / 2000) (4053694389835369 / 7812500000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry148C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry148C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (965496630716056907 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry148C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (932183743924057961 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry148C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (21696576639832449 / 50000000000000000) (233 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry148C_hz2 hx hc) (lowGeometry148C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (103442638977900671 / 250000000000000000) (233 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry148C_hz38 hx hc) (lowGeometry148C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry148C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (267 / 500) (1069 / 2000) θ) : B (103442638977900671 / 250000000000000000) (233 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry148C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry148C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (267 / 500) (1069 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (48492477 / 125000000) (111053083 / 200000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65540789 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry148C_hz12 hx hc).2
  have hrp := (lowGeometry148C_hz16 hx hc).2
  have hbn := (lowGeometry148C_hz21 hx hc).2
  have hlo := (lowGeometry148C_hz40 hx hc).1
  have hhi := (lowGeometry148C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry149W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (1069 / 2000) (107 / 200) θ := hc

theorem lowGeometry149W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry149W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (93 / 200) (931 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry149W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (99417 / 400000) (99617 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry149W_hz0 hx hc) (lowGeometry149W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (99617 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry149W_hz3 hx hc) (lowGeometry149W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (5579454498425451 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry149W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (16738363495276353 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry149W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (1069 / 1000) (107 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry149W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry149W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry149W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (107 / 2000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry149W_hz7 hx hc) (lowGeometry149W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (30113363495276353 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry149W_hz6 hx hc) (lowGeometry149W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (30113363495276353 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry149W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry149W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (1069 / 50) (107 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry149W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (107 / 40000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry149W_hz13 hx hc) (lowGeometry149W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (30782113495276353 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry149W_hz12 hx hc) (lowGeometry149W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (30782113495276353 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry149W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry149W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (107 / 1600000) (θ * x) := bmul (lowGeometry149W_hz0 hx hc) (lowGeometry149W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (35954301075269 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry149W_hz17 hx hc) (lowGeometry149W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (2998095273472351 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry149W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (8994285820417053 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry149W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (8994285820417053 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry149W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry149W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (1069 / 250) (107 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry149W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry149W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (23925927359247751 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry149W_hz22 hx hc) (lowGeometry149W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry149W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry149W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry149W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry149W_hz26 hx hc) (lowGeometry149W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry149W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (50301381690764721 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry149W_hz24 hx hc) (lowGeometry149W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (133994285820417053 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry149W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (229817198496302317 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry149W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (93 / 200) (534899529500143643 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry149W_hz2 hx hc) (lowGeometry149W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (93 / 200) (146300227797727091 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry149W_hz33 hx hc) (lowGeometry149W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (93 / 200) (146300227797727091 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry149W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry149W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (116005714179582947 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry149W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (3364331430578773 / 3906250000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry149W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (400490013496097137 / 1000000000000000000) (931 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry149W_hz2 hx hc) (lowGeometry149W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (5471697371958319 / 15625000000000000) (931 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry149W_hz38 hx hc) (lowGeometry149W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (5471697371958319 / 15625000000000000) (931 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry149W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry149W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1069 / 2000) (107 / 200) θ) :
    OverlapGuard n θ lowWideWindow (311797489 / 1000000000) (16633597 / 25000000) ∧ radiusMinus n θ lowWideWindow ≤ (60226727 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry149W_hz12 hx hc).2
  have hrp := (lowGeometry149W_hz16 hx hc).2
  have hbn := (lowGeometry149W_hz21 hx hc).2
  have hlo := (lowGeometry149W_hz40 hx hc).1
  have hhi := (lowGeometry149W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry149C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (1069 / 2000) (107 / 200) θ := hc

theorem lowGeometry149C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry149C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (93 / 200) (931 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry149C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (99417 / 400000) (99617 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry149C_hz0 hx hc) (lowGeometry149C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (99617 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry149C_hz3 hx hc) (lowGeometry149C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (5579454498425451 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry149C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (16068828955465299 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry149C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (1069 / 1000) (107 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry149C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry149C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry149C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (8358037392982877 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry149C_hz7 hx hc) (lowGeometry149C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (32784903741431053 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry149C_hz6 hx hc) (lowGeometry149C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (32784903741431053 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry149C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry149C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (834889 / 100000) (83567 / 10000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry149C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (83567 / 80000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry149C_hz13 hx hc) (lowGeometry149C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (33307197491431053 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry149C_hz12 hx hc) (lowGeometry149C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (33307197491431053 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry149C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry149C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (107 / 1600000) (θ * x) := bmul (lowGeometry149C_hz0 hx hc) (lowGeometry149C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (35954301075269 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry149C_hz17 hx hc) (lowGeometry149C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (2998095273472351 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry149C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (8634514387600371 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry149C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (8634514387600371 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry149C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry149C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (349563 / 200000) (34989 / 20000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry149C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry149C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (19559445616185037 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry149C_hz22 hx hc) (lowGeometry149C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry149C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry149C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry149C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry149C_hz26 hx hc) (lowGeometry149C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry149C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 0 (20179836545369071 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry149C_hz24 hx hc) (lowGeometry149C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (258634514387600371 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry149C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B 1 (1070268992520157813 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry149C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (93 / 200) (249105108009066731 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry149C_hz2 hx hc) (lowGeometry149C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (93 / 200) (518390052563502533 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry149C_hz33 hx hc) (lowGeometry149C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (93 / 200) (518390052563502533 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry149C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry149C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (241365485612399629 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry149C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (233029190579637969 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry149C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (216717147239063311 / 500000000000000000) (931 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry149C_hz2 hx hc) (lowGeometry149C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (413254457932757551 / 1000000000000000000) (931 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry149C_hz38 hx hc) (lowGeometry149C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry149C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1069 / 2000) (107 / 200) θ) : B (413254457932757551 / 1000000000000000000) (931 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry149C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry149C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1069 / 2000) (107 / 200) θ) :
    OverlapGuard n θ lowCoreWindow (4843063 / 12500000) (11095319 / 20000000) ∧ radiusMinus n θ lowCoreWindow ≤ (4098113 / 62500000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry149C_hz12 hx hc).2
  have hrp := (lowGeometry149C_hz16 hx hc).2
  have hbn := (lowGeometry149C_hz21 hx hc).2
  have hlo := (lowGeometry149C_hz40 hx hc).1
  have hhi := (lowGeometry149C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry150W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (107 / 200) (1071 / 2000) θ := hc

theorem lowGeometry150W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry150W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (929 / 2000) (93 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry150W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (99403 / 400000) (99603 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry150W_hz0 hx hc) (lowGeometry150W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (99603 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry150W_hz3 hx hc) (lowGeometry150W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (2789531210615863 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry150W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (8368593631847589 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry150W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (107 / 100) (1071 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry150W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry150W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry150W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1071 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry150W_hz7 hx hc) (lowGeometry150W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (15062343631847589 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry150W_hz6 hx hc) (lowGeometry150W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (15062343631847589 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry150W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry150W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (107 / 5) (1071 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry150W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1071 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry150W_hz13 hx hc) (lowGeometry150W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (15397031131847589 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry150W_hz12 hx hc) (lowGeometry150W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (15397031131847589 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry150W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry150W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1071 / 16000000) (θ * x) := bmul (lowGeometry150W_hz0 hx hc) (lowGeometry150W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (18013320775027 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry150W_hz17 hx hc) (lowGeometry150W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (480177577486023 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry150W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1440532732458069 / 20000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry150W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1440532732458069 / 20000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry150W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry150W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (107 / 25) (1071 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry150W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry150W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (23948288039022749 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry150W_hz22 hx hc) (lowGeometry150W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry150W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry150W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry150W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry150W_hz26 hx hc) (lowGeometry150W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry150W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (25174196163929447 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry150W_hz24 hx hc) (lowGeometry150W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (21440532732458069 / 20000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry150W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (1149241109629014677 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry150W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (929 / 2000) (21375884639099673 / 40000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry150W_hz2 hx hc) (lowGeometry150W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (929 / 2000) (584745508305350719 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry150W_hz33 hx hc) (lowGeometry150W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (929 / 2000) (584745508305350719 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry150W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry150W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (18559467267541931 / 20000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry150W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (215283640784350219 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry150W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (199998502288661353 / 500000000000000000) (93 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry150W_hz2 hx hc) (lowGeometry150W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (87412153062365953 / 250000000000000000) (93 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry150W_hz38 hx hc) (lowGeometry150W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (87412153062365953 / 250000000000000000) (93 / 200) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry150W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry150W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (107 / 200) (1071 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (1216029 / 3906250) (664860349 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (96399 / 800000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry150W_hz12 hx hc).2
  have hrp := (lowGeometry150W_hz16 hx hc).2
  have hbn := (lowGeometry150W_hz21 hx hc).2
  have hlo := (lowGeometry150W_hz40 hx hc).1
  have hhi := (lowGeometry150W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry150C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (107 / 200) (1071 / 2000) θ := hc

theorem lowGeometry150C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry150C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (929 / 2000) (93 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry150C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (99403 / 400000) (99603 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry150C_hz0 hx hc) (lowGeometry150C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (99603 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry150C_hz3 hx hc) (lowGeometry150C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (2789531210615863 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry150C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (16067699773147371 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry150C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (107 / 100) (1071 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry150C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry150C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry150C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (8365848642882861 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry150C_hz7 hx hc) (lowGeometry150C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (32799397058913093 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry150C_hz6 hx hc) (lowGeometry150C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (32799397058913093 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry150C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry150C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (83567 / 10000) (836451 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry150C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (836451 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry150C_hz13 hx hc) (lowGeometry150C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (33322178933913093 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry150C_hz12 hx hc) (lowGeometry150C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (33322178933913093 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry150C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry150C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (1071 / 16000000) (θ * x) := bmul (lowGeometry150C_hz0 hx hc) (lowGeometry150C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (18013320775027 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry150C_hz17 hx hc) (lowGeometry150C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (480177577486023 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry150C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (4321598197374207 / 125000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry150C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (4321598197374207 / 125000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry150C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry150C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (34989 / 20000) (350217 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry150C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry150C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (9788862735950549 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry150C_hz22 hx hc) (lowGeometry150C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry150C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry150C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry150C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry150C_hz26 hx hc) (lowGeometry150C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry150C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 0 (10099348102845923 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry150C_hz24 hx hc) (lowGeometry150C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (129321598197374207 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry150C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B 1 (66896303041292399 / 62500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry150C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (929 / 2000) (497708494627215449 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry150C_hz2 hx hc) (lowGeometry150C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (929 / 2000) (103581438166581459 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry150C_hz33 hx hc) (lowGeometry150C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (929 / 2000) (103581438166581459 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry150C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry150C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (120678401802625793 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry150C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (932049706344703759 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry150C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (27058568037319681 / 62500000000000000) (93 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry150C_hz2 hx hc) (lowGeometry150C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (8254767847828461 / 20000000000000000) (93 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry150C_hz38 hx hc) (lowGeometry150C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry150C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (107 / 200) (1071 / 2000) θ) : B (8254767847828461 / 20000000000000000) (93 / 200) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry150C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry150C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (107 / 200) (1071 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (77390067 / 200000000) (554266399 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (13119759 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry150C_hz12 hx hc).2
  have hrp := (lowGeometry150C_hz16 hx hc).2
  have hbn := (lowGeometry150C_hz21 hx hc).2
  have hlo := (lowGeometry150C_hz40 hx hc).1
  have hhi := (lowGeometry150C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry151W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (1071 / 2000) (67 / 125) θ := hc

theorem lowGeometry151W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry151W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (58 / 125) (929 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry151W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (31059 / 125000) (62243 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry151W_hz0 hx hc) (lowGeometry151W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (62243 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry151W_hz3 hx hc) (lowGeometry151W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (5578664714786147 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry151W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (16735994144358441 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry151W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (1071 / 1000) (134 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry151W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry151W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry151W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (67 / 1250) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry151W_hz7 hx hc) (lowGeometry151W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (30135994144358441 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry151W_hz6 hx hc) (lowGeometry151W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (30135994144358441 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry151W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry151W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (1071 / 50) (536 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry151W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (67 / 25000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry151W_hz13 hx hc) (lowGeometry151W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (30805994144358441 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry151W_hz12 hx hc) (lowGeometry151W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (30805994144358441 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry151W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry151W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (67 / 1000000) (θ * x) := bmul (lowGeometry151W_hz0 hx hc) (lowGeometry151W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (72198275862069 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry151W_hz17 hx hc) (lowGeometry151W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1201651162876057 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry151W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (3604953488628171 / 50000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry151W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (3604953488628171 / 50000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry151W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry151W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (1071 / 250) (536 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry151W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry151W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (23970648718797747 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry151W_hz22 hx hc) (lowGeometry151W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry151W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry151W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry151W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry151W_hz26 hx hc) (lowGeometry151W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry151W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (50395402964953067 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry151W_hz24 hx hc) (lowGeometry151W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (53604953488628171 / 50000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry151W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (1149396415407195809 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry151W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (58 / 125) (266947317478321227 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry151W_hz2 hx hc) (lowGeometry151W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (58 / 125) (584290037921595521 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry151W_hz33 hx hc) (lowGeometry151W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (58 / 125) (584290037921595521 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry151W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry151W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (46395046511371829 / 50000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry151W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (53812508519808883 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry151W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (399504063251061147 / 1000000000000000000) (929 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry151W_hz2 hx hc) (lowGeometry151W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (4363858253576351 / 12500000000000000) (929 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry151W_hz38 hx hc) (lowGeometry151W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (4363858253576351 / 12500000000000000) (929 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry151W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry151W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1071 / 2000) (67 / 125) θ) :
    OverlapGuard n θ lowWideWindow (7770237 / 25000000) (664376641 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (120543977 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry151W_hz12 hx hc).2
  have hrp := (lowGeometry151W_hz16 hx hc).2
  have hbn := (lowGeometry151W_hz21 hx hc).2
  have hlo := (lowGeometry151W_hz40 hx hc).1
  have hhi := (lowGeometry151W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry151C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (1071 / 2000) (67 / 125) θ := hc

theorem lowGeometry151C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry151C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (58 / 125) (929 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry151C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (31059 / 125000) (62243 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry151C_hz0 hx hc) (lowGeometry151C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (62243 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry151C_hz3 hx hc) (lowGeometry151C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (5578664714786147 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry151C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (32133108757168207 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry151C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (1071 / 1000) (134 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry151C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry151C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry151C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1674731978556569 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry151C_hz7 hx hc) (lowGeometry151C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (65627748328299587 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry151C_hz6 hx hc) (lowGeometry151C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (65627748328299587 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry151C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry151C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (836451 / 100000) (52327 / 6250) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry151C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (52327 / 50000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry151C_hz13 hx hc) (lowGeometry151C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (66674288328299587 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry151C_hz12 hx hc) (lowGeometry151C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (66674288328299587 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry151C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry151C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (67 / 1000000) (θ * x) := bmul (lowGeometry151C_hz0 hx hc) (lowGeometry151C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (72198275862069 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry151C_hz17 hx hc) (lowGeometry151C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1201651162876057 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry151C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (17303776745415221 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry151C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (17303776745415221 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry151C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry151C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (350217 / 200000) (21909 / 12500) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry151C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry151C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (9798002663808579 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry151C_hz22 hx hc) (lowGeometry151C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry151C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry151C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry151C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry151C_hz26 hx hc) (lowGeometry151C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry151C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 0 (1010877793300731 / 50000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry151C_hz24 hx hc) (lowGeometry151C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (517303776745415221 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry151C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B 1 (42816511589611263 / 40000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry151C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (58 / 125) (62150842604295099 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry151C_hz2 hx hc) (lowGeometry151C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (58 / 125) (129356074175093853 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry151C_hz33 hx hc) (lowGeometry151C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (58 / 125) (129356074175093853 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry151C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry151C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (482696223254584779 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry151C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (465991287888479903 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry151C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (432439915160509349 / 1000000000000000000) (929 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry151C_hz2 hx hc) (lowGeometry151C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (412222359294494729 / 1000000000000000000) (929 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry151C_hz38 hx hc) (lowGeometry151C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry151C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1071 / 2000) (67 / 125) θ) : B (412222359294494729 / 1000000000000000000) (929 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry151C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry151C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1071 / 2000) (67 / 125) θ) :
    OverlapGuard n θ lowCoreWindow (3864557 / 10000000) (553766763 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65627749 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry151C_hz12 hx hc).2
  have hrp := (lowGeometry151C_hz16 hx hc).2
  have hbn := (lowGeometry151C_hz21 hx hc).2
  have hlo := (lowGeometry151C_hz40 hx hc).1
  have hhi := (lowGeometry151C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry152W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (67 / 125) (1073 / 2000) θ := hc

theorem lowGeometry152W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry152W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (927 / 2000) (58 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry152W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (62109 / 250000) (31117 / 125000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry152W_hz0 hx hc) (lowGeometry152W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (31117 / 1000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry152W_hz3 hx hc) (lowGeometry152W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (557826137788469 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry152W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1673478413365407 / 25000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry152W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (134 / 125) (1073 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry152W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry152W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry152W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1073 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry152W_hz7 hx hc) (lowGeometry152W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (3014728413365407 / 25000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry152W_hz6 hx hc) (lowGeometry152W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (3014728413365407 / 25000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry152W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry152W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (536 / 25) (1073 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry152W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1073 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry152W_hz13 hx hc) (lowGeometry152W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (3081790913365407 / 25000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry152W_hz12 hx hc) (lowGeometry152W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (3081790913365407 / 25000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry152W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry152W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1073 / 16000000) (θ * x) := bmul (lowGeometry152W_hz0 hx hc) (lowGeometry152W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (144687162891047 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry152W_hz17 hx hc) (lowGeometry152W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (481143908436629 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry152W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1443431725309887 / 20000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry152W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1443431725309887 / 20000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry152W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry152W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (536 / 125) (1073 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry152W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry152W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (4798601879714549 / 100000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry152W_hz22 hx hc) (lowGeometry152W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry152W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry152W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry152W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry152W_hz26 hx hc) (lowGeometry152W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry152W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1261060340051181 / 25000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry152W_hz24 hx hc) (lowGeometry152W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (21443431725309887 / 20000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry152W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (1149551910395066393 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry152W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (927 / 2000) (533392086423310807 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry152W_hz2 hx hc) (lowGeometry152W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (927 / 2000) (583834500025358047 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry152W_hz33 hx hc) (lowGeometry152W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (927 / 2000) (583834500025358047 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry152W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry152W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (18556568274690113 / 20000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry152W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (26902048916659031 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry152W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (399011189531886747 / 1000000000000000000) (58 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry152W_hz2 hx hc) (lowGeometry152W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (348568775929839507 / 1000000000000000000) (58 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry152W_hz38 hx hc) (lowGeometry152W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (348568775929839507 / 1000000000000000000) (58 / 125) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry152W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry152W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (67 / 125) (1073 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (310315657 / 1000000000) (331946377 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (120589137 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry152W_hz12 hx hc).2
  have hrp := (lowGeometry152W_hz16 hx hc).2
  have hbn := (lowGeometry152W_hz21 hx hc).2
  have hlo := (lowGeometry152W_hz40 hx hc).1
  have hhi := (lowGeometry152W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry152C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (67 / 125) (1073 / 2000) θ := hc

theorem lowGeometry152C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry152C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (927 / 2000) (58 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry152C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (62109 / 250000) (31117 / 125000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry152C_hz0 hx hc) (lowGeometry152C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (31117 / 1000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry152C_hz3 hx hc) (lowGeometry152C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (557826137788469 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry152C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (6426157107323163 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry152C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (134 / 125) (1073 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry152C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry152C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry152C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (8381471142682829 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry152C_hz7 hx hc) (lowGeometry152C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (65656670107347131 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry152C_hz6 hx hc) (lowGeometry152C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (65656670107347131 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry152C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry152C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (52327 / 6250) (838013 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry152C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (838013 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry152C_hz13 hx hc) (lowGeometry152C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (66704186357347131 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry152C_hz12 hx hc) (lowGeometry152C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (66704186357347131 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry152C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry152C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (1073 / 16000000) (θ * x) := bmul (lowGeometry152C_hz0 hx hc) (lowGeometry152C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (144687162891047 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry152C_hz17 hx hc) (lowGeometry152C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (481143908436629 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry152C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (4330295175929661 / 125000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry152C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (4330295175929661 / 125000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry152C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry152C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (21909 / 12500) (350871 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry152C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry152C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (19614285183333219 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry152C_hz22 hx hc) (lowGeometry152C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry152C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry152C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry152C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry152C_hz26 hx hc) (lowGeometry152C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry152C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 0 (4047283105267479 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry152C_hz24 hx hc) (lowGeometry152C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (129330295175929661 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry152C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B 1 (1070484816018758077 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry152C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (927 / 2000) (124176238658175937 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry152C_hz2 hx hc) (lowGeometry152C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (927 / 2000) (516941370159041143 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry152C_hz33 hx hc) (lowGeometry152C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (927 / 2000) (516941370159041143 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry152C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry152C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (120669704824070339 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry152C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (232978842597252231 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry152C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (107985693543826409 / 250000000000000000) (58 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry152C_hz2 hx hc) (lowGeometry152C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (411706358648968241 / 1000000000000000000) (58 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry152C_hz38 hx hc) (lowGeometry152C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry152C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (67 / 125) (1073 / 2000) θ) : B (411706358648968241 / 1000000000000000000) (58 / 125) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry152C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry152C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (67 / 125) (1073 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (77192227 / 200000000) (276633521 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65656671 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry152C_hz12 hx hc).2
  have hrp := (lowGeometry152C_hz16 hx hc).2
  have hbn := (lowGeometry152C_hz21 hx hc).2
  have hlo := (lowGeometry152C_hz40 hx hc).1
  have hhi := (lowGeometry152C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry153W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (1073 / 2000) (537 / 1000) θ := hc

theorem lowGeometry153W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry153W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (463 / 1000) (927 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry153W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (496799 / 2000000) (497799 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry153W_hz0 hx hc) (lowGeometry153W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (497799 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry153W_hz3 hx hc) (lowGeometry153W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (5577852409305933 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry153W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (16733557227917799 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry153W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (1073 / 1000) (537 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry153W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry153W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry153W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (537 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry153W_hz7 hx hc) (lowGeometry153W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (30158557227917799 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry153W_hz6 hx hc) (lowGeometry153W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (30158557227917799 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry153W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry153W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (1073 / 50) (537 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry153W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (537 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry153W_hz13 hx hc) (lowGeometry153W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (30829807227917799 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry153W_hz12 hx hc) (lowGeometry153W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (30829807227917799 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry153W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry153W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (537 / 8000000) (θ * x) := bmul (lowGeometry153W_hz0 hx hc) (lowGeometry153W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (72489200863931 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry153W_hz17 hx hc) (lowGeometry153W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (12040697725956831 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry153W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (36122093177870493 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry153W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (36122093177870493 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry153W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry153W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (1073 / 250) (537 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry153W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry153W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (9606148031339097 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry153W_hz22 hx hc) (lowGeometry153W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry153W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry153W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry153W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry153W_hz26 hx hc) (lowGeometry153W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry153W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (12622356059785353 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry153W_hz24 hx hc) (lowGeometry153W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (536122093177870493 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry153W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (229941519034737001 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry153W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (463 / 1000) (532889470363003 / 1000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry153W_hz2 hx hc) (lowGeometry153W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (463 / 1000) (145844723650536103 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry153W_hz33 hx hc) (lowGeometry153W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (463 / 1000) (145844723650536103 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry153W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry153W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (463877906822129507 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry153W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (43036542487536053 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry153W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (7970367668691677 / 20000000000000000) (927 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry153W_hz2 hx hc) (lowGeometry153W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (174014479597721219 / 500000000000000000) (927 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry153W_hz38 hx hc) (lowGeometry153W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (174014479597721219 / 500000000000000000) (927 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry153W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry153W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1073 / 2000) (537 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (154910977 / 500000000) (663408691 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (120634229 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry153W_hz12 hx hc).2
  have hrp := (lowGeometry153W_hz16 hx hc).2
  have hbn := (lowGeometry153W_hz21 hx hc).2
  have hlo := (lowGeometry153W_hz40 hx hc).1
  have hhi := (lowGeometry153W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry153C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (1073 / 2000) (537 / 1000) θ := hc

theorem lowGeometry153C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry153C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (463 / 1000) (927 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry153C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (496799 / 2000000) (497799 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry153C_hz0 hx hc) (lowGeometry153C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (497799 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry153C_hz3 hx hc) (lowGeometry153C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (5577852409305933 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry153C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (1285137195104087 / 40000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry153C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (1073 / 1000) (537 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry153C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry153C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry153C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (8389282392582813 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry153C_hz7 hx hc) (lowGeometry153C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (65685559447933427 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry153C_hz6 hx hc) (lowGeometry153C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (65685559447933427 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry153C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry153C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (838013 / 100000) (419397 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry153C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (419397 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry153C_hz13 hx hc) (lowGeometry153C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (66734051947933427 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry153C_hz12 hx hc) (lowGeometry153C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (66734051947933427 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry153C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry153C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (537 / 8000000) (θ * x) := bmul (lowGeometry153C_hz0 hx hc) (lowGeometry153C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (72489200863931 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry153C_hz17 hx hc) (lowGeometry153C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (12040697725956831 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry153C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (17338604725377837 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry153C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (17338604725377837 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry153C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry153C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (350871 / 200000) (175599 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry153C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry153C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (61351765747029 / 3125000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry153C_hz22 hx hc) (lowGeometry153C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry153C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry153C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry153C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry153C_hz26 hx hc) (lowGeometry153C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry153C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 0 (2025527518666017 / 100000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry153C_hz24 hx hc) (lowGeometry153C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (517338604725377837 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry153C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B 1 (1070556927756802927 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry153C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (463 / 1000) (496203136015278157 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry153C_hz2 hx hc) (lowGeometry153C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (463 / 1000) (516458411201938327 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry153C_hz33 hx hc) (lowGeometry153C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (463 / 1000) (516458411201938327 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry153C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry153C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (482661395274622163 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry153C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (93184808995378023 / 100000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry153C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (215722832824300123 / 500000000000000000) (927 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry153C_hz2 hx hc) (lowGeometry153C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (102797597615485019 / 250000000000000000) (927 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry153C_hz38 hx hc) (lowGeometry153C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry153C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1073 / 2000) (537 / 1000) θ) : B (102797597615485019 / 250000000000000000) (927 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry153C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry153C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1073 / 2000) (537 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (385466639 / 1000000000) (552767237 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (1642139 / 25000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry153C_hz12 hx hc).2
  have hrp := (lowGeometry153C_hz16 hx hc).2
  have hbn := (lowGeometry153C_hz21 hx hc).2
  have hlo := (lowGeometry153C_hz40 hx hc).1
  have hhi := (lowGeometry153C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry154W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (537 / 1000) (43 / 80) θ := hc

theorem lowGeometry154W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry154W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (37 / 80) (463 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry154W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (19869 / 80000) (19909 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry154W_hz0 hx hc) (lowGeometry154W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (19909 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry154W_hz3 hx hc) (lowGeometry154W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (5577437807811039 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry154W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (16732313423433117 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry154W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (537 / 500) (43 / 40) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry154W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry154W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry154W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (43 / 800) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry154W_hz7 hx hc) (lowGeometry154W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (30169813423433117 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry154W_hz6 hx hc) (lowGeometry154W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (30169813423433117 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry154W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry154W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (537 / 25) (43 / 2) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry154W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (43 / 16000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry154W_hz13 hx hc) (lowGeometry154W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (30841688423433117 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry154W_hz12 hx hc) (lowGeometry154W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (30841688423433117 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry154W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry154W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (43 / 640000) (θ * x) := bmul (lowGeometry154W_hz0 hx hc) (lowGeometry154W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (145270270270271 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry154W_hz17 hx hc) (lowGeometry154W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (1205281171637021 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry154W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (3615843514911063 / 50000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry154W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (3615843514911063 / 50000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry154W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry154W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (537 / 125) (43 / 10) (θ * (8 : ℝ)) := bmul (lowGeometry154W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry154W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (48075461516245481 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry154W_hz22 hx hc) (lowGeometry154W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry154W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry154W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry154W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry154W_hz26 hx hc) (lowGeometry154W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry154W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (789631794941181 / 15625000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry154W_hz24 hx hc) (lowGeometry154W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (53615843514911063 / 50000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry154W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (1149863470326172277 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry154W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (37 / 80) (106477357352203553 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry154W_hz2 hx hc) (lowGeometry154W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (37 / 80) (582923221637253349 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry154W_hz33 hx hc) (lowGeometry154W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (37 / 80) (582923221637253349 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry154W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry154W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (46384156485088937 / 50000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry154W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (215148997283321809 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry154W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (199012822487072673 / 500000000000000000) (463 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry154W_hz2 hx hc) (lowGeometry154W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (173744605048954881 / 500000000000000000) (463 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry154W_hz38 hx hc) (lowGeometry154W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (173744605048954881 / 500000000000000000) (463 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry154W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry154W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (537 / 1000) (43 / 80) θ) :
    OverlapGuard n θ lowWideWindow (77332093 / 250000000) (13258489 / 20000000) ∧ radiusMinus n θ lowWideWindow ≤ (60339627 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry154W_hz12 hx hc).2
  have hrp := (lowGeometry154W_hz16 hx hc).2
  have hbn := (lowGeometry154W_hz21 hx hc).2
  have hlo := (lowGeometry154W_hz40 hx hc).1
  have hhi := (lowGeometry154W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry154C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (537 / 1000) (43 / 80) θ := hc

theorem lowGeometry154C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry154C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (37 / 80) (463 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry154C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (19869 / 80000) (19909 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry154C_hz0 hx hc) (lowGeometry154C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (19909 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry154C_hz3 hx hc) (lowGeometry154C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (5577437807811039 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry154C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (6425208354598317 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry154C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (537 / 500) (43 / 40) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry154C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry154C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry154C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (8397093642482797 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry154C_hz7 hx hc) (lowGeometry154C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (65714416342922773 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry154C_hz6 hx hc) (lowGeometry154C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (65714416342922773 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry154C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry154C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (419397 / 50000) (33583 / 4000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry154C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (33583 / 32000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry154C_hz13 hx hc) (lowGeometry154C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (66763885092922773 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry154C_hz12 hx hc) (lowGeometry154C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (66763885092922773 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry154C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry154C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (43 / 640000) (θ * x) := bmul (lowGeometry154C_hz0 hx hc) (lowGeometry154C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (145270270270271 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry154C_hz17 hx hc) (lowGeometry154C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (1205281171637021 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry154C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (6942419548629241 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry154C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (6942419548629241 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry154C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry154C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (175599 / 100000) (14061 / 8000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry154C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry154C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (19650844894765341 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry154C_hz22 hx hc) (lowGeometry154C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry154C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry154C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry154C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry154C_hz26 hx hc) (lowGeometry154C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry154C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 0 (4054826969396589 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry154C_hz24 hx hc) (lowGeometry154C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (206942419548629241 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry154C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B 1 (535314562608011073 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry154C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (37 / 80) (247850642487509127 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry154C_hz2 hx hc) (lowGeometry154C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (37 / 80) (515975419822001199 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry154C_hz33 hx hc) (lowGeometry154C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (37 / 80) (515975419822001199 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry154C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry154C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (193057580451370759 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry154C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (37271229369737493 / 40000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry154C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (215474294793794881 / 500000000000000000) (463 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry154C_hz2 hx hc) (lowGeometry154C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (410674454740606817 / 1000000000000000000) (463 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry154C_hz38 hx hc) (lowGeometry154C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry154C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (537 / 1000) (43 / 80) θ) : B (410674454740606817 / 1000000000000000000) (463 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry154C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry154C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (537 / 1000) (43 / 80) θ) :
    OverlapGuard n θ lowCoreWindow (192486107 / 500000000) (552267347 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65714417 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry154C_hz12 hx hc).2
  have hrp := (lowGeometry154C_hz16 hx hc).2
  have hbn := (lowGeometry154C_hz21 hx hc).2
  have hlo := (lowGeometry154C_hz40 hx hc).1
  have hhi := (lowGeometry154C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry155W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (43 / 80) (269 / 500) θ := hc

theorem lowGeometry155W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry155W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (231 / 500) (37 / 80) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry155W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (9933 / 40000) (9953 / 40000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry155W_hz0 hx hc) (lowGeometry155W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (9953 / 320000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry155W_hz3 hx hc) (lowGeometry155W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (1115403514428747 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry155W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (3346210543286241 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry155W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (43 / 40) (269 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry155W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry155W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry155W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (269 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry155W_hz7 hx hc) (lowGeometry155W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (6036210543286241 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry155W_hz6 hx hc) (lowGeometry155W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (6036210543286241 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry155W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry155W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (43 / 2) (538 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry155W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (269 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry155W_hz13 hx hc) (lowGeometry155W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (6170710543286241 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry155W_hz12 hx hc) (lowGeometry155W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (6170710543286241 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry155W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry155W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (269 / 4000000) (θ * x) := bmul (lowGeometry155W_hz0 hx hc) (lowGeometry155W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (145562770562771 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry155W_hz17 hx hc) (lowGeometry155W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (754058732799259 / 62500000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry155W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (2262176198397777 / 31250000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry155W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (2262176198397777 / 31250000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry155W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry155W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (43 / 10) (538 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry155W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry155W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (48120182875795477 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry155W_hz22 hx hc) (lowGeometry155W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry155W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry155W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry155W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry155W_hz26 hx hc) (lowGeometry155W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry155W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (50583445513329757 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry155W_hz24 hx hc) (lowGeometry155W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (33512176198397777 / 31250000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry155W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (230003907287543497 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry155W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (231 / 500) (531884035602444337 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry155W_hz2 hx hc) (lowGeometry155W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (231 / 500) (291233740557887047 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry155W_hz33 hx hc) (lowGeometry155W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (231 / 500) (291233740557887047 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry155W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry155W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (28987823801602223 / 31250000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry155W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (215115245760700507 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry155W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (49691621770721817 / 125000000000000000) (37 / 80) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry155W_hz2 hx hc) (lowGeometry155W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (346949528652444779 / 1000000000000000000) (37 / 80) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry155W_hz38 hx hc) (lowGeometry155W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (346949528652444779 / 1000000000000000000) (37 / 80) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry155W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry155W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (43 / 80) (269 / 500) θ) :
    OverlapGuard n θ lowWideWindow (308834911 / 1000000000) (20701251 / 31250000) ∧ radiusMinus n θ lowWideWindow ≤ (120724211 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry155W_hz12 hx hc).2
  have hrp := (lowGeometry155W_hz16 hx hc).2
  have hbn := (lowGeometry155W_hz21 hx hc).2
  have hlo := (lowGeometry155W_hz40 hx hc).1
  have hhi := (lowGeometry155W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry155C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (43 / 80) (269 / 500) θ := hc

theorem lowGeometry155C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry155C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (231 / 500) (37 / 80) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry155C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (9933 / 40000) (9953 / 40000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry155C_hz0 hx hc) (lowGeometry155C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (9953 / 320000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry155C_hz3 hx hc) (lowGeometry155C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (1115403514428747 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry155C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (16061810607773957 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry155C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (43 / 40) (269 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry155C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry155C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry155C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (8404904892382781 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry155C_hz7 hx hc) (lowGeometry155C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (32871620392539519 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry155C_hz6 hx hc) (lowGeometry155C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (32871620392539519 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry155C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry155C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (33583 / 4000) (210089 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry155C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (210089 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry155C_hz13 hx hc) (lowGeometry155C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (33396842892539519 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry155C_hz12 hx hc) (lowGeometry155C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (33396842892539519 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry155C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry155C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (269 / 4000000) (θ * x) := bmul (lowGeometry155C_hz0 hx hc) (lowGeometry155C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (145562770562771 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry155C_hz17 hx hc) (lowGeometry155C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (754058732799259 / 62500000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry155C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (6949405281477971 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry155C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (6949405281477971 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry155C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry155C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (14061 / 8000) (87963 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry155C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry155C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (9834562375240701 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry155C_hz22 hx hc) (lowGeometry155C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry155C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry155C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry155C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry155C_hz26 hx hc) (lowGeometry155C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry155C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 0 (507324862682643 / 25000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry155C_hz24 hx hc) (lowGeometry155C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (206949405281477971 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry155C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B 1 (535350704329467779 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry155C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (231 / 500) (7737490648511839 / 15625000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry155C_hz2 hx hc) (lowGeometry155C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (231 / 500) (64436549501507927 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry155C_hz33 hx hc) (lowGeometry155C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (231 / 500) (64436549501507927 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry155C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry155C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (193050594718522029 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry155C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (931713303029376137 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry155C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (17218061839982871 / 40000000000000000) (37 / 80) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry155C_hz2 hx hc) (lowGeometry155C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (82031710298453211 / 200000000000000000) (37 / 80) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry155C_hz38 hx hc) (lowGeometry155C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry155C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (43 / 80) (269 / 500) θ) : B (82031710298453211 / 200000000000000000) (37 / 80) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry155C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry155C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (43 / 80) (269 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (192238929 / 500000000) (137941843 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (65743241 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry155C_hz12 hx hc).2
  have hrp := (lowGeometry155C_hz16 hx hc).2
  have hbn := (lowGeometry155C_hz21 hx hc).2
  have hlo := (lowGeometry155C_hz40 hx hc).1
  have hhi := (lowGeometry155C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry156W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (269 / 500) (1077 / 2000) θ := hc

theorem lowGeometry156W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry156W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (923 / 2000) (231 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry156W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (248287 / 1000000) (248787 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry156W_hz0 hx hc) (lowGeometry156W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (248787 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry156W_hz3 hx hc) (lowGeometry156W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (5576591701030299 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry156W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (16729775103090897 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry156W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (269 / 250) (1077 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry156W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry156W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry156W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1077 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry156W_hz7 hx hc) (lowGeometry156W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (30192275103090897 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry156W_hz6 hx hc) (lowGeometry156W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (30192275103090897 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry156W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry156W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (538 / 25) (1077 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry156W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1077 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry156W_hz13 hx hc) (lowGeometry156W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (30865400103090897 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry156W_hz12 hx hc) (lowGeometry156W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (30865400103090897 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry156W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry156W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1077 / 16000000) (θ * x) := bmul (lowGeometry156W_hz0 hx hc) (lowGeometry156W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (72927952329361 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry156W_hz17 hx hc) (lowGeometry156W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (47176100757773 / 3906250000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry156W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (141528302273319 / 1953125000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry156W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (141528302273319 / 1953125000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry156W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry156W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (538 / 125) (1077 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry156W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry156W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (48164904235345473 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry156W_hz22 hx hc) (lowGeometry156W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry156W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry156W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry156W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry156W_hz26 hx hc) (lowGeometry156W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry156W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (5063045615042393 / 100000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry156W_hz24 hx hc) (lowGeometry156W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (2094653302273319 / 1953125000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry156W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (1150175794095592649 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry156W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (923 / 2000) (132845304218040951 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry156W_hz2 hx hc) (lowGeometry156W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (923 / 2000) (291005836511293867 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry156W_hz33 hx hc) (lowGeometry156W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (923 / 2000) (291005836511293867 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry156W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry156W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (1811596697726681 / 1953125000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry156W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (107540728879979417 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry156W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (397040371024884007 / 1000000000000000000) (231 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry156W_hz2 hx hc) (lowGeometry156W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (346409914874460077 / 1000000000000000000) (231 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry156W_hz38 hx hc) (lowGeometry156W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (346409914874460077 / 1000000000000000000) (231 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry156W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry156W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (269 / 500) (1077 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (308341571 / 1000000000) (165488859 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (120769101 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry156W_hz12 hx hc).2
  have hrp := (lowGeometry156W_hz16 hx hc).2
  have hbn := (lowGeometry156W_hz21 hx hc).2
  have hlo := (lowGeometry156W_hz40 hx hc).1
  have hhi := (lowGeometry156W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry156C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (269 / 500) (1077 / 2000) θ := hc

theorem lowGeometry156C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry156C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (923 / 2000) (231 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry156C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (248287 / 1000000) (248787 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry156C_hz0 hx hc) (lowGeometry156C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (248787 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry156C_hz3 hx hc) (lowGeometry156C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (5576591701030299 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry156C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (32121168197934523 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry156C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (269 / 250) (1077 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry156C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry156C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry156C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1682543228456553 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry156C_hz7 hx hc) (lowGeometry156C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (65772032767065583 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry156C_hz6 hx hc) (lowGeometry156C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (65772032767065583 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry156C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry156C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (210089 / 25000) (841137 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry156C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (841137 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry156C_hz13 hx hc) (lowGeometry156C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (66823454017065583 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry156C_hz12 hx hc) (lowGeometry156C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (66823454017065583 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry156C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry156C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (1077 / 16000000) (θ * x) := bmul (lowGeometry156C_hz0 hx hc) (lowGeometry156C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (72927952329361 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry156C_hz17 hx hc) (lowGeometry156C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (47176100757773 / 3906250000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry156C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (17390997783345439 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry156C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (17390997783345439 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry156C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry156C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (87963 / 50000) (352179 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry156C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry156C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (9843702303098731 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry156C_hz22 hx hc) (lowGeometry156C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry156C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry156C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry156C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry156C_hz26 hx hc) (lowGeometry156C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry156C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 0 (10155927083814247 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry156C_hz24 hx hc) (lowGeometry156C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (517390997783345439 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry156C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B 1 (53538688917449153 / 50000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry156C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (923 / 2000) (247348742798615087 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry156C_hz2 hx hc) (lowGeometry156C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (923 / 2000) (128752334941214667 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry156C_hz33 hx hc) (lowGeometry156C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (923 / 2000) (128752334941214667 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry156C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry156C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (482609002216654561 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry156C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (931645796082219547 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry156C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (671803960768663 / 1562500000000000) (231 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry156C_hz2 hx hc) (lowGeometry156C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (204821340362157913 / 500000000000000000) (231 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry156C_hz38 hx hc) (lowGeometry156C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry156C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (269 / 500) (1077 / 2000) θ) : B (204821340362157913 / 500000000000000000) (231 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry156C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry156C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (269 / 500) (1077 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (95995893 / 250000000) (34454207 / 62500000) ∧ radiusMinus n θ lowCoreWindow ≤ (65772033 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry156C_hz12 hx hc).2
  have hrp := (lowGeometry156C_hz16 hx hc).2
  have hbn := (lowGeometry156C_hz21 hx hc).2
  have hlo := (lowGeometry156C_hz40 hx hc).1
  have hhi := (lowGeometry156C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry157W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (1077 / 2000) (539 / 1000) θ := hc

theorem lowGeometry157W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry157W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (461 / 1000) (923 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry157W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (496497 / 2000000) (497497 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry157W_hz0 hx hc) (lowGeometry157W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (497497 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry157W_hz3 hx hc) (lowGeometry157W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (5576160193179533 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry157W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (16728480579538599 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry157W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (1077 / 1000) (539 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry157W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry157W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry157W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (539 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry157W_hz7 hx hc) (lowGeometry157W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (30203480579538599 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry157W_hz6 hx hc) (lowGeometry157W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (30203480579538599 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry157W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry157W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (1077 / 50) (539 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry157W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (539 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry157W_hz13 hx hc) (lowGeometry157W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (30877230579538599 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry157W_hz12 hx hc) (lowGeometry157W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (30877230579538599 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry157W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry157W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (539 / 8000000) (θ * x) := bmul (lowGeometry157W_hz0 hx hc) (lowGeometry157W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (146149674620391 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry157W_hz17 hx hc) (lowGeometry157W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (12089237966902257 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry157W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (36267713900706771 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry157W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (36267713900706771 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry157W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry157W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (1077 / 250) (539 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry157W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry157W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (48209625594895469 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry157W_hz22 hx hc) (lowGeometry157W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry157W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry157W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry157W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry157W_hz26 hx hc) (lowGeometry157W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry157W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (50677466787518103 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry157W_hz24 hx hc) (lowGeometry157W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (536267713900706771 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry157W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (1150332243889161161 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry157W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (461 / 1000) (132719582638711969 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry157W_hz2 hx hc) (lowGeometry157W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (461 / 1000) (581555797342365979 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry157W_hz33 hx hc) (lowGeometry157W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (461 / 1000) (581555797342365979 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry157W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry157W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (463732286099293229 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry157W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (53761908292719187 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry157W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (396547835567096723 / 1000000000000000000) (923 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry157W_hz2 hx hc) (lowGeometry157W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (17293518438978931 / 50000000000000000) (923 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry157W_hz38 hx hc) (lowGeometry157W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (17293518438978931 / 50000000000000000) (923 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry157W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry157W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1077 / 2000) (539 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (6156967 / 20000000) (661470663 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (120813923 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry157W_hz12 hx hc).2
  have hrp := (lowGeometry157W_hz16 hx hc).2
  have hbn := (lowGeometry157W_hz21 hx hc).2
  have hlo := (lowGeometry157W_hz40 hx hc).1
  have hhi := (lowGeometry157W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry157C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (1077 / 2000) (539 / 1000) θ := hc

theorem lowGeometry157C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry157C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (461 / 1000) (923 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry157C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (496497 / 2000000) (497497 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry157C_hz0 hx hc) (lowGeometry157C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (497497 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry157C_hz3 hx hc) (lowGeometry157C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (5576160193179533 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry157C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (32118682712714111 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry157C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (1077 / 1000) (539 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry157C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry157C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry157C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (8420527392182749 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry157C_hz7 hx hc) (lowGeometry157C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (65800792281445107 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry157C_hz6 hx hc) (lowGeometry157C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (65800792281445107 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry157C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry157C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (841137 / 100000) (420959 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry157C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (420959 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry157C_hz13 hx hc) (lowGeometry157C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (66853189781445107 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry157C_hz12 hx hc) (lowGeometry157C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (66853189781445107 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry157C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry157C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (539 / 8000000) (θ * x) := bmul (lowGeometry157C_hz0 hx hc) (lowGeometry157C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (146149674620391 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry157C_hz17 hx hc) (lowGeometry157C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (12089237966902257 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry157C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (34817005344678501 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry157C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (34817005344678501 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry157C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry157C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (352179 / 200000) (176253 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry157C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry157C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (19705684461913523 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry157C_hz22 hx hc) (lowGeometry157C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry157C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry157C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry157C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry157C_hz26 hx hc) (lowGeometry157C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry157C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 0 (20330713827951269 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry157C_hz24 hx hc) (lowGeometry157C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (1034817005344678501 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry157C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B 1 (535423117275264187 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry157C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (461 / 1000) (98839107449013769 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry157C_hz2 hx hc) (lowGeometry157C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (461 / 1000) (257263125536510057 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry157C_hz33 hx hc) (lowGeometry157C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (461 / 1000) (257263125536510057 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry157C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry157C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (965182994655321499 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry157C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (931578213171814369 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry157C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (53682194534025803 / 125000000000000000) (923 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry157C_hz2 hx hc) (lowGeometry157C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (81825368488851031 / 200000000000000000) (923 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry157C_hz38 hx hc) (lowGeometry157C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry157C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1077 / 2000) (539 / 1000) θ) : B (81825368488851031 / 200000000000000000) (923 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry157C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry157C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1077 / 2000) (539 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (76697871 / 200000000) (8605737 / 15625000) ∧ radiusMinus n θ lowCoreWindow ≤ (65800793 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry157C_hz12 hx hc).2
  have hrp := (lowGeometry157C_hz16 hx hc).2
  have hbn := (lowGeometry157C_hz21 hx hc).2
  have hlo := (lowGeometry157C_hz40 hx hc).1
  have hhi := (lowGeometry157C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry158W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (539 / 1000) (1079 / 2000) θ := hc

theorem lowGeometry158W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry158W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (921 / 2000) (461 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry158W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (496419 / 2000000) (497419 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry158W_hz0 hx hc) (lowGeometry158W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (497419 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry158W_hz3 hx hc) (lowGeometry158W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (5575723047282747 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry158W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (16727169141848241 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry158W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (539 / 500) (1079 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry158W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry158W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry158W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1079 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry158W_hz7 hx hc) (lowGeometry158W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (30214669141848241 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry158W_hz6 hx hc) (lowGeometry158W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (30214669141848241 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry158W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry158W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (539 / 25) (1079 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry158W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1079 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry158W_hz13 hx hc) (lowGeometry158W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (30889044141848241 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry158W_hz12 hx hc) (lowGeometry158W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (30889044141848241 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry158W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry158W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1079 / 16000000) (θ * x) := bmul (lowGeometry158W_hz0 hx hc) (lowGeometry158W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (73222041259501 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry158W_hz17 hx hc) (lowGeometry158W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (12101408286600449 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry158W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (36304224859801347 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry158W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (36304224859801347 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry158W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry158W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (539 / 125) (1079 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry158W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry158W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (6031793369305683 / 125000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry158W_hz22 hx hc) (lowGeometry158W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry158W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry158W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry158W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry158W_hz26 hx hc) (lowGeometry158W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry158W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (2028979096984491 / 40000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry158W_hz24 hx hc) (lowGeometry158W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (536304224859801347 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry158W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (1150488886409889461 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry158W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (921 / 2000) (265187688317479521 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry158W_hz2 hx hc) (lowGeometry158W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (921 / 2000) (581099854059571317 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry158W_hz33 hx hc) (lowGeometry158W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (921 / 2000) (581099854059571317 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry158W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry158W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (463695775140198653 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry158W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (215013771882869671 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry158W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (396055367808245933 / 1000000000000000000) (461 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry158W_hz2 hx hc) (lowGeometry158W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (172665445191816829 / 500000000000000000) (461 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry158W_hz38 hx hc) (lowGeometry158W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (172665445191816829 / 500000000000000000) (461 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry158W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry158W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (539 / 1000) (1079 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (1229421 / 4000000) (660985713 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (120858677 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry158W_hz12 hx hc).2
  have hrp := (lowGeometry158W_hz16 hx hc).2
  have hbn := (lowGeometry158W_hz21 hx hc).2
  have hlo := (lowGeometry158W_hz40 hx hc).1
  have hhi := (lowGeometry158W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry158C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (539 / 1000) (1079 / 2000) θ := hc

theorem lowGeometry158C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry158C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (921 / 2000) (461 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry158C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (496419 / 2000000) (497419 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry158C_hz0 hx hc) (lowGeometry158C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (497419 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry158C_hz3 hx hc) (lowGeometry158C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (5575723047282747 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry158C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (32116164752348623 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry158C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (539 / 500) (1079 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry158C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry158C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry158C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (8428338642082733 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry158C_hz7 hx hc) (lowGeometry158C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (13165903864135911 / 200000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry158C_hz6 hx hc) (lowGeometry158C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (13165903864135911 / 200000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry158C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry158C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (420959 / 50000) (842699 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry158C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (842699 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry158C_hz13 hx hc) (lowGeometry158C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (13376578614135911 / 200000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry158C_hz12 hx hc) (lowGeometry158C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (13376578614135911 / 200000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry158C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry158C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1079 / 16000000) (θ * x) := bmul (lowGeometry158C_hz0 hx hc) (lowGeometry158C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (73222041259501 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry158C_hz17 hx hc) (lowGeometry158C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (12101408286600449 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry158C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (17426027932704647 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry158C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (17426027932704647 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry158C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry158C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (176253 / 100000) (352833 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry158C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry158C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (1232747769851849 / 62500000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry158C_hz22 hx hc) (lowGeometry158C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry158C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry158C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry158C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry158C_hz26 hx hc) (lowGeometry158C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry158C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 0 (5087393372068511 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry158C_hz24 hx hc) (lowGeometry158C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (517426027932704647 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry158C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B 1 (1070918777528864199 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry158C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (921 / 2000) (123423389110201599 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry158C_hz2 hx hc) (lowGeometry158C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (921 / 2000) (12851078248227011 / 25000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry158C_hz33 hx hc) (lowGeometry158C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (921 / 2000) (12851078248227011 / 25000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry158C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry158C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (482573972067295353 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry158C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (465755277033613511 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry158C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (428960610147958043 / 1000000000000000000) (461 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry158C_hz2 hx hc) (lowGeometry158C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (408611036659683999 / 1000000000000000000) (461 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry158C_hz38 hx hc) (lowGeometry158C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry158C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (539 / 1000) (1079 / 2000) θ) : B (408611036659683999 / 1000000000000000000) (461 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry158C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry158C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (539 / 1000) (1079 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (382995209 / 1000000000) (275133469 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (822869 / 12500000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry158C_hz12 hx hc).2
  have hrp := (lowGeometry158C_hz16 hx hc).2
  have hbn := (lowGeometry158C_hz21 hx hc).2
  have hlo := (lowGeometry158C_hz40 hx hc).1
  have hhi := (lowGeometry158C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry159W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (1079 / 2000) (27 / 50) θ := hc

theorem lowGeometry159W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry159W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (23 / 50) (921 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry159W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (24817 / 100000) (24867 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry159W_hz0 hx hc) (lowGeometry159W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (24867 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry159W_hz3 hx hc) (lowGeometry159W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (5575280262013741 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry159W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (16725840786041223 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry159W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (1079 / 1000) (27 / 25) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry159W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry159W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry159W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (27 / 500) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry159W_hz7 hx hc) (lowGeometry159W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (30225840786041223 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry159W_hz6 hx hc) (lowGeometry159W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (30225840786041223 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry159W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry159W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (1079 / 50) (108 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry159W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (27 / 10000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry159W_hz13 hx hc) (lowGeometry159W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (30900840786041223 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry159W_hz12 hx hc) (lowGeometry159W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (30900840786041223 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry159W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry159W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (27 / 400000) (θ * x) := bmul (lowGeometry159W_hz0 hx hc) (lowGeometry159W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (146739130434783 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry159W_hz17 hx hc) (lowGeometry159W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (12113592796308741 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry159W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (36340778388926223 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry159W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (36340778388926223 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry159W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry159W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (1079 / 250) (108 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry159W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry159W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (2414953415699773 / 50000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry159W_hz22 hx hc) (lowGeometry159W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry159W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry159W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry159W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry159W_hz26 hx hc) (lowGeometry159W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry159W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (3173218003856653 / 62500000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry159W_hz24 hx hc) (lowGeometry159W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (536340778388926223 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry159W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (1150645722251357081 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry159W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (23 / 50) (33117022193546871 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry159W_hz2 hx hc) (lowGeometry159W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (23 / 50) (9072560049350881 / 15625000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry159W_hz33 hx hc) (lowGeometry159W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (23 / 50) (9072560049350881 / 15625000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry159W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry159W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (463659221611073777 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry159W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (26872484223123353 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry159W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (98890741941093939 / 250000000000000000) (921 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry159W_hz2 hx hc) (lowGeometry159W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (86197869925667327 / 250000000000000000) (921 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry159W_hz38 hx hc) (lowGeometry159W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (86197869925667327 / 250000000000000000) (921 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry159W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry159W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1079 / 2000) (27 / 50) θ) :
    OverlapGuard n θ lowWideWindow (30686227 / 100000000) (330250293 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (30225841 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry159W_hz12 hx hc).2
  have hrp := (lowGeometry159W_hz16 hx hc).2
  have hbn := (lowGeometry159W_hz21 hx hc).2
  have hlo := (lowGeometry159W_hz40 hx hc).1
  have hhi := (lowGeometry159W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry159C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (1079 / 2000) (27 / 50) θ := hc

theorem lowGeometry159C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry159C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (23 / 50) (921 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry159C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (24817 / 100000) (24867 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry159C_hz0 hx hc) (lowGeometry159C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (24867 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry159C_hz3 hx hc) (lowGeometry159C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (5575280262013741 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry159C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (32113614309199149 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry159C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (1079 / 1000) (27 / 25) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry159C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry159C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry159C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (8436149891982717 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry159C_hz7 hx hc) (lowGeometry159C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (65858213877130017 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry159C_hz6 hx hc) (lowGeometry159C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (65858213877130017 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry159C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry159C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (842699 / 100000) (21087 / 2500) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry159C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (21087 / 20000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry159C_hz13 hx hc) (lowGeometry159C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (66912563877130017 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry159C_hz12 hx hc) (lowGeometry159C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (66912563877130017 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry159C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry159C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (27 / 400000) (θ * x) := bmul (lowGeometry159C_hz0 hx hc) (lowGeometry159C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (146739130434783 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry159C_hz17 hx hc) (lowGeometry159C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (12113592796308741 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry159C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (1395485890134767 / 40000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry159C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (1395485890134767 / 40000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry159C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry159C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (352833 / 200000) (8829 / 5000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry159C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry159C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (3948448834669129 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry159C_hz22 hx hc) (lowGeometry159C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry159C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry159C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry159C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry159C_hz26 hx hc) (lowGeometry159C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry159C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 0 (20368433148596819 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry159C_hz24 hx hc) (lowGeometry159C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (41395485890134767 / 40000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry159C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B 1 (214198281510043323 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry159C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (23 / 50) (1926529465534667 / 3906250000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry159C_hz2 hx hc) (lowGeometry159C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (23 / 50) (513559976325471571 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry159C_hz33 hx hc) (lowGeometry159C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (23 / 50) (513559976325471571 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry159C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry159C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (38604514109865233 / 40000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry159C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (465721409268369957 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry159C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (10711592413172509 / 25000000000000000) (921 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry159C_hz2 hx hc) (lowGeometry159C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (408095263378303541 / 1000000000000000000) (921 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry159C_hz38 hx hc) (lowGeometry159C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry159C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1079 / 2000) (27 / 50) θ) : B (408095263378303541 / 1000000000000000000) (921 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry159C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry159C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1079 / 2000) (27 / 50) θ) :
    OverlapGuard n θ lowCoreWindow (382501131 / 1000000000) (4398133 / 8000000) ∧ radiusMinus n θ lowCoreWindow ≤ (32929107 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry159C_hz12 hx hc).2
  have hrp := (lowGeometry159C_hz16 hx hc).2
  have hbn := (lowGeometry159C_hz21 hx hc).2
  have hlo := (lowGeometry159C_hz40 hx hc).1
  have hhi := (lowGeometry159C_hz35 hx hc).2
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
