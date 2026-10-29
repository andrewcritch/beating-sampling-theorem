import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part199 BstLean.Part255 BstLean.Part264b
theorem lowGeometry32W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (119 / 250) (953 / 2000) θ := hc

theorem lowGeometry32W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry32W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (1047 / 2000) (131 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry32W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (124593 / 500000) (124843 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry32W_hz0 hx hc) (lowGeometry32W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (124843 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry32W_hz3 hx hc) (lowGeometry32W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (5586658213995197 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry32W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (16759974641985591 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry32W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (119 / 125) (953 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry32W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry32W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry32W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (953 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry32W_hz7 hx hc) (lowGeometry32W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (28672474641985591 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry32W_hz6 hx hc) (lowGeometry32W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (28672474641985591 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry32W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry32W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (476 / 25) (953 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry32W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (953 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry32W_hz13 hx hc) (lowGeometry32W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (29268099641985591 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry32W_hz12 hx hc) (lowGeometry32W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (29268099641985591 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry32W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry32W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (953 / 16000000) (θ * x) := bmul (lowGeometry32W_hz0 hx hc) (lowGeometry32W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (14222182425979 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry32W_hz17 hx hc) (lowGeometry32W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (10666651743065019 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry32W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (31999955229195057 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry32W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (31999955229195057 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry32W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry32W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (476 / 125) (953 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry32W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry32W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (21309727825572997 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry32W_hz22 hx hc) (lowGeometry32W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry32W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry32W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry32W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry32W_hz26 hx hc) (lowGeometry32W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry32W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (44801137150746523 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry32W_hz24 hx hc) (lowGeometry32W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (531999955229195057 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry32W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (1132095809455462181 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry32W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (1047 / 2000) (593218204154662183 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry32W_hz2 hx hc) (lowGeometry32W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (1047 / 2000) (319009670652704353 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry32W_hz33 hx hc) (lowGeometry32W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (1047 / 2000) (319009670652704353 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry32W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry32W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (468000044770804943 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry32W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (219024041905475431 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry32W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (28664771484379097 / 62500000000000000) (131 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry32W_hz2 hx hc) (lowGeometry32W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (413835206599319029 / 1000000000000000000) (131 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry32W_hz38 hx hc) (lowGeometry32W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (413835206599319029 / 1000000000000000000) (131 / 250) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry32W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry32W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (119 / 250) (953 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (370464087 / 1000000000) (90084161 / 125000000) ∧ radiusMinus n θ lowWideWindow ≤ (114689899 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry32W_hz12 hx hc).2
  have hrp := (lowGeometry32W_hz16 hx hc).2
  have hbn := (lowGeometry32W_hz21 hx hc).2
  have hlo := (lowGeometry32W_hz40 hx hc).1
  have hhi := (lowGeometry32W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry32C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (119 / 250) (953 / 2000) θ := hc

theorem lowGeometry32C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry32C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (1047 / 2000) (131 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry32C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (124593 / 500000) (124843 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry32C_hz0 hx hc) (lowGeometry32C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (124843 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry32C_hz3 hx hc) (lowGeometry32C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (5586658213995197 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry32C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (6435830262522467 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry32C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (119 / 125) (953 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry32C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry32C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry32C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (29776484618738997 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry32C_hz7 hx hc) (lowGeometry32C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (15488908982837833 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry32C_hz6 hx hc) (lowGeometry32C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (15488908982837833 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry32C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry32C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (92939 / 12500) (744293 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry32C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (744293 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry32C_hz13 hx hc) (lowGeometry32C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (15721500545337833 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry32C_hz12 hx hc) (lowGeometry32C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (15721500545337833 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry32C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry32C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (953 / 16000000) (θ * x) := bmul (lowGeometry32C_hz0 hx hc) (lowGeometry32C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (14222182425979 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry32C_hz17 hx hc) (lowGeometry32C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (10666651743065019 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry32C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (6143991404005451 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry32C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (6143991404005451 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry32C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry32C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (38913 / 25000) (311631 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry32C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry32C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (696828099896237 / 40000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry32C_hz22 hx hc) (lowGeometry32C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry32C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry32C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry32C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry32C_hz26 hx hc) (lowGeometry32C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry32C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 0 (3594651257520883 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry32C_hz24 hx hc) (lowGeometry32C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (206143991404005451 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry32C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B 1 (66398976862460427 / 62500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry32C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (1047 / 2000) (27834451100743411 / 50000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry32C_hz2 hx hc) (lowGeometry32C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (1047 / 2000) (114932455660494527 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry32C_hz33 hx hc) (lowGeometry32C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (1047 / 2000) (114932455660494527 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry32C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry32C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (193856008595994549 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry32C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (939503801719257811 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry32C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (61478780025003933 / 125000000000000000) (131 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry32C_hz2 hx hc) (lowGeometry32C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (473856983912427049 / 1000000000000000000) (131 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry32C_hz38 hx hc) (lowGeometry32C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry32C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (119 / 250) (953 / 2000) θ) : B (473856983912427049 / 1000000000000000000) (131 / 250) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry32C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry32C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (119 / 250) (953 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (222910539 / 500000000) (306308689 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15488909 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry32C_hz12 hx hc).2
  have hrp := (lowGeometry32C_hz16 hx hc).2
  have hbn := (lowGeometry32C_hz21 hx hc).2
  have hlo := (lowGeometry32C_hz40 hx hc).1
  have hhi := (lowGeometry32C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry33W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (953 / 2000) (477 / 1000) θ := hc

theorem lowGeometry33W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry33W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (523 / 1000) (1047 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry33W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (498419 / 2000000) (499419 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry33W_hz0 hx hc) (lowGeometry33W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (499419 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry33W_hz3 hx hc) (lowGeometry33W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (5586921110951899 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry33W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (16760763332855697 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry33W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (953 / 1000) (477 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry33W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry33W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry33W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (477 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry33W_hz7 hx hc) (lowGeometry33W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (28685763332855697 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry33W_hz6 hx hc) (lowGeometry33W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (28685763332855697 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry33W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry33W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (953 / 50) (477 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry33W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (477 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry33W_hz13 hx hc) (lowGeometry33W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (29282013332855697 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry33W_hz12 hx hc) (lowGeometry33W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (29282013332855697 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry33W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry33W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (477 / 8000000) (θ * x) := bmul (lowGeometry33W_hz0 hx hc) (lowGeometry33W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (28501434034417 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry33W_hz17 hx hc) (lowGeometry33W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (427093874716401 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry33W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (1281281624149203 / 20000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry33W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (1281281624149203 / 20000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry33W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry33W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (953 / 250) (477 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry33W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry33W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (4266417701069599 / 100000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry33W_hz22 hx hc) (lowGeometry33W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry33W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry33W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry33W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry33W_hz26 hx hc) (lowGeometry33W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry33W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (5606018473480087 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry33W_hz24 hx hc) (lowGeometry33W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (21281281624149203 / 20000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry33W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (1132232368915876349 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry33W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (523 / 1000) (592723645127461269 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry33W_hz2 hx hc) (lowGeometry33W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (523 / 1000) (127514358583060393 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry33W_hz33 hx hc) (lowGeometry33W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (523 / 1000) (127514358583060393 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry33W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry33W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (18718718375850797 / 20000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry33W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (218994011021508937 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry33W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (57266933882124587 / 125000000000000000) (1047 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry33W_hz2 hx hc) (lowGeometry33W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (103321830817289 / 250000000000000) (1047 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry33W_hz38 hx hc) (lowGeometry33W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (103321830817289 / 250000000000000) (1047 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry33W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry33W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (953 / 2000) (477 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (369955191 / 1000000000) (720211003 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (57371527 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry33W_hz12 hx hc).2
  have hrp := (lowGeometry33W_hz16 hx hc).2
  have hbn := (lowGeometry33W_hz21 hx hc).2
  have hlo := (lowGeometry33W_hz40 hx hc).1
  have hhi := (lowGeometry33W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry33C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (953 / 2000) (477 / 1000) θ := hc

theorem lowGeometry33C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry33C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (523 / 1000) (1047 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry33C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (498419 / 2000000) (499419 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry33C_hz0 hx hc) (lowGeometry33C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (499419 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry33C_hz3 hx hc) (lowGeometry33C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (5586921110951899 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry33C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (32180665599082939 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry33C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (953 / 1000) (477 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry33C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry33C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry33C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (29807729618338933 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry33C_hz7 hx hc) (lowGeometry33C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (3874274701088867 / 62500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry33C_hz6 hx hc) (lowGeometry33C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (3874274701088867 / 62500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry33C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry33C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (744293 / 100000) (372537 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry33C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (372537 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry33C_hz13 hx hc) (lowGeometry33C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (3932483607338867 / 62500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry33C_hz12 hx hc) (lowGeometry33C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (3932483607338867 / 62500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry33C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry33C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (477 / 8000000) (θ * x) := bmul (lowGeometry33C_hz0 hx hc) (lowGeometry33C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (28501434034417 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry33C_hz17 hx hc) (lowGeometry33C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (427093874716401 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry33C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (3843844872447609 / 125000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry33C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (3843844872447609 / 125000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry33C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry33C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (311631 / 200000) (155979 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry33C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry33C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (8719491176560993 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry33C_hz22 hx hc) (lowGeometry33C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry33C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry33C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry33C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry33C_hz26 hx hc) (lowGeometry33C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry33C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 0 (1799211594792719 / 100000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry33C_hz24 hx hc) (lowGeometry33C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (128843844872447609 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry33C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B 1 (531223563568491009 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry33C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (523 / 1000) (556191071056210087 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry33C_hz2 hx hc) (lowGeometry33C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (523 / 1000) (574183187004137277 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry33C_hz33 hx hc) (lowGeometry33C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (523 / 1000) (574183187004137277 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry33C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry33C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (121156155127552391 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry33C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (939444091218658529 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry33C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (49132925970735841 / 100000000000000000) (1047 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry33C_hz2 hx hc) (lowGeometry33C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (23666857187971561 / 50000000000000000) (1047 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry33C_hz38 hx hc) (lowGeometry33C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry33C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (953 / 2000) (477 / 1000) θ) : B (23666857187971561 / 50000000000000000) (1047 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry33C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry33C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (953 / 2000) (477 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (22265893 / 50000000) (612128021 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15497099 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry33C_hz12 hx hc).2
  have hrp := (lowGeometry33C_hz16 hx hc).2
  have hbn := (lowGeometry33C_hz21 hx hc).2
  have hlo := (lowGeometry33C_hz40 hx hc).1
  have hhi := (lowGeometry33C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry34W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (477 / 1000) (191 / 400) θ := hc

theorem lowGeometry34W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry34W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (209 / 400) (523 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry34W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (99693 / 400000) (99893 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry34W_hz0 hx hc) (lowGeometry34W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (99893 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry34W_hz3 hx hc) (lowGeometry34W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (2793589201189037 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry34W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (8380767603567111 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry34W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (477 / 500) (191 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry34W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry34W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry34W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (191 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry34W_hz7 hx hc) (lowGeometry34W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (14349517603567111 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry34W_hz6 hx hc) (lowGeometry34W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (14349517603567111 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry34W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry34W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (477 / 25) (191 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry34W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (191 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry34W_hz13 hx hc) (lowGeometry34W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (14647955103567111 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry34W_hz12 hx hc) (lowGeometry34W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (14647955103567111 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry34W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry34W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (191 / 3200000) (θ * x) := bmul (lowGeometry34W_hz0 hx hc) (lowGeometry34W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (57117224880383 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry34W_hz17 hx hc) (lowGeometry34W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1068805172895257 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry34W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (3206415518685771 / 50000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry34W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (3206415518685771 / 50000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry34W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry34W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (477 / 125) (191 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry34W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry34W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (21354449185122993 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry34W_hz22 hx hc) (lowGeometry34W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry34W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry34W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry34W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry34W_hz26 hx hc) (lowGeometry34W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry34W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (44895158424934869 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry34W_hz24 hx hc) (lowGeometry34W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (53206415518685771 / 50000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry34W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (1132369060938818417 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry34W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (209 / 400) (592229018871002033 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry34W_hz2 hx hc) (lowGeometry34W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (209 / 400) (318562088647968451 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry34W_hz33 hx hc) (lowGeometry34W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (209 / 400) (318562088647968451 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry34W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry34W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (46793584481314229 / 50000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry34W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (855327948675739 / 976562500000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry34W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (228817332829733697 / 500000000000000000) (523 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry34W_hz2 hx hc) (lowGeometry34W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (16509580289381301 / 40000000000000000) (523 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry34W_hz38 hx hc) (lowGeometry34W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (16509580289381301 / 40000000000000000) (523 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry34W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry34W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (477 / 1000) (191 / 400) θ) :
    OverlapGuard n θ lowWideWindow (369446429 / 1000000000) (179937133 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (114796141 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry34W_hz12 hx hc).2
  have hrp := (lowGeometry34W_hz16 hx hc).2
  have hbn := (lowGeometry34W_hz21 hx hc).2
  have hlo := (lowGeometry34W_hz40 hx hc).1
  have hhi := (lowGeometry34W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry34C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (477 / 1000) (191 / 400) θ := hc

theorem lowGeometry34C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry34C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (209 / 400) (523 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry34C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (99693 / 400000) (99893 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry34C_hz0 hx hc) (lowGeometry34C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (99893 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry34C_hz3 hx hc) (lowGeometry34C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (2793589201189037 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry34C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (32182147597697707 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry34C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (477 / 500) (191 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry34C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry34C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry34C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (29838974617938869 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry34C_hz7 hx hc) (lowGeometry34C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1938160069238643 / 31250000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry34C_hz6 hx hc) (lowGeometry34C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1938160069238643 / 31250000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry34C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry34C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (372537 / 50000) (149171 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry34C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (149171 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry34C_hz13 hx hc) (lowGeometry34C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1967295030176143 / 31250000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry34C_hz12 hx hc) (lowGeometry34C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1967295030176143 / 31250000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry34C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry34C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (191 / 3200000) (θ * x) := bmul (lowGeometry34C_hz0 hx hc) (lowGeometry34C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (57117224880383 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry34C_hz17 hx hc) (lowGeometry34C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (1068805172895257 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry34C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (15390794489691701 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry34C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (15390794489691701 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry34C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry34C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (155979 / 100000) (62457 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry34C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry34C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (17457262208838047 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry34C_hz22 hx hc) (lowGeometry34C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry34C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry34C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry34C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry34C_hz26 hx hc) (lowGeometry34C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry34C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 0 (3602195121649993 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry34C_hz24 hx hc) (lowGeometry34C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (515390794489691701 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry34C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B 1 (531255342089431251 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry34C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (209 / 400) (555693087825545089 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry34C_hz2 hx hc) (lowGeometry34C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (209 / 400) (286852031716897527 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry34C_hz33 hx hc) (lowGeometry34C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (209 / 400) (286852031716897527 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry34C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry34C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (484609205510308299 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry34C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (939384328261328893 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry34C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (245414155758272173 / 500000000000000000) (523 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry34C_hz2 hx hc) (lowGeometry34C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (472817335908294381 / 1000000000000000000) (523 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry34C_hz38 hx hc) (lowGeometry34C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry34C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (477 / 1000) (191 / 400) θ) : B (472817335908294381 / 1000000000000000000) (523 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry34C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry34C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (477 / 1000) (191 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (222407359 / 500000000) (24465543 / 40000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62021123 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry34C_hz12 hx hc).2
  have hrp := (lowGeometry34C_hz16 hx hc).2
  have hbn := (lowGeometry34C_hz21 hx hc).2
  have hlo := (lowGeometry34C_hz40 hx hc).1
  have hhi := (lowGeometry34C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry35W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (191 / 400) (239 / 500) θ := hc

theorem lowGeometry35W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry35W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (261 / 500) (209 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry35W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (49851 / 200000) (49951 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry35W_hz0 hx hc) (lowGeometry35W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (49951 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry35W_hz3 hx hc) (lowGeometry35W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (1117486017809619 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry35W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (3352458053428857 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry35W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (191 / 200) (239 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry35W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry35W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry35W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (239 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry35W_hz7 hx hc) (lowGeometry35W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (5742458053428857 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry35W_hz6 hx hc) (lowGeometry35W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (5742458053428857 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry35W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry35W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (191 / 10) (478 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry35W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (239 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry35W_hz13 hx hc) (lowGeometry35W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (5861958053428857 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry35W_hz12 hx hc) (lowGeometry35W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (5861958053428857 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry35W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry35W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (239 / 4000000) (θ * x) := bmul (lowGeometry35W_hz0 hx hc) (lowGeometry35W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (14307950191571 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry35W_hz17 hx hc) (lowGeometry35W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (10698766355639701 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry35W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (32096299066919103 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry35W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (32096299066919103 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry35W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry35W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (191 / 50) (478 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry35W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry35W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (42753619729795981 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry35W_hz22 hx hc) (lowGeometry35W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry35W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry35W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry35W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry35W_hz26 hx hc) (lowGeometry35W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry35W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (561777113275363 / 12500000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry35W_hz24 hx hc) (lowGeometry35W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (532096299066919103 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry35W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (1132505885922848861 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry35W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (261 / 500) (59173432539468853 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry35W_hz2 hx hc) (lowGeometry35W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (261 / 500) (63667649445671757 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry35W_hz33 hx hc) (lowGeometry35W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (261 / 500) (63667649445671757 / 100000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry35W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry35W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (467903700933080897 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry35W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (218933873346874009 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry35W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (45713392754827293 / 100000000000000000) (209 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry35W_hz2 hx hc) (lowGeometry35W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (41219175848624389 / 100000000000000000) (209 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry35W_hz38 hx hc) (lowGeometry35W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (41219175848624389 / 100000000000000000) (209 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry35W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry35W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (191 / 400) (239 / 500) θ) :
    OverlapGuard n θ lowWideWindow (1844689 / 5000000) (359642937 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (57424581 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry35W_hz12 hx hc).2
  have hrp := (lowGeometry35W_hz16 hx hc).2
  have hbn := (lowGeometry35W_hz21 hx hc).2
  have hlo := (lowGeometry35W_hz40 hx hc).1
  have hhi := (lowGeometry35W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry35C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (191 / 400) (239 / 500) θ := hc

theorem lowGeometry35C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry35C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (261 / 500) (209 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry35C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (49851 / 200000) (49951 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry35C_hz0 hx hc) (lowGeometry35C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (49951 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry35C_hz3 hx hc) (lowGeometry35C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (1117486017809619 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry35C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (8045899328229257 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry35C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (191 / 200) (239 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry35C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry35C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry35C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (5974043923507761 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry35C_hz7 hx hc) (lowGeometry35C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (62053816930455833 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry35C_hz6 hx hc) (lowGeometry35C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (62053816930455833 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry35C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry35C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (149171 / 20000) (186659 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry35C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (186659 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry35C_hz13 hx hc) (lowGeometry35C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (62987111930455833 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry35C_hz12 hx hc) (lowGeometry35C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (62987111930455833 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry35C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry35C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (239 / 4000000) (θ * x) := bmul (lowGeometry35C_hz0 hx hc) (lowGeometry35C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (14307950191571 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry35C_hz17 hx hc) (lowGeometry35C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (10698766355639701 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry35C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (30812447104242339 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry35C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (30812447104242339 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry35C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry35C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (62457 / 40000) (78153 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry35C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry35C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (4368885516138527 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry35C_hz22 hx hc) (lowGeometry35C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry35C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry35C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry35C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry35C_hz26 hx hc) (lowGeometry35C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry35C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 0 (901491763428637 / 50000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry35C_hz24 hx hc) (lowGeometry35C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (1030812447104242339 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry35C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B 1 (1062574301105036411 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry35C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (261 / 500) (22207802893095261 / 40000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry35C_hz2 hx hc) (lowGeometry35C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (261 / 500) (114644981519190853 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry35C_hz33 hx hc) (lowGeometry35C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (261 / 500) (114644981519190853 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry35C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry35C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (969187552895757661 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry35C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (469662256344033527 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry35C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (245163697811585501 / 500000000000000000) (209 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry35C_hz2 hx hc) (lowGeometry35C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (236148780177299131 / 500000000000000000) (209 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry35C_hz38 hx hc) (lowGeometry35C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry35C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (191 / 400) (239 / 500) θ) : B (236148780177299131 / 500000000000000000) (209 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry35C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry35C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (191 / 400) (239 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (111077913 / 250000000) (611149039 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62053817 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry35C_hz12 hx hc).2
  have hrp := (lowGeometry35C_hz16 hx hc).2
  have hbn := (lowGeometry35C_hz21 hx hc).2
  have hlo := (lowGeometry35C_hz40 hx hc).1
  have hhi := (lowGeometry35C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry36W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (239 / 500) (957 / 2000) θ := hc

theorem lowGeometry36W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry36W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (1043 / 2000) (261 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry36W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (249277 / 1000000) (249777 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry36W_hz0 hx hc) (lowGeometry36W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (249777 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry36W_hz3 hx hc) (lowGeometry36W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (1396919042929833 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry36W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (4190757128789499 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry36W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (239 / 250) (957 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry36W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry36W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry36W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (957 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry36W_hz7 hx hc) (lowGeometry36W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (7181382128789499 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry36W_hz6 hx hc) (lowGeometry36W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (7181382128789499 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry36W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry36W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (478 / 25) (957 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry36W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (957 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry36W_hz13 hx hc) (lowGeometry36W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (7330913378789499 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry36W_hz12 hx hc) (lowGeometry36W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (7330913378789499 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry36W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry36W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (957 / 16000000) (θ * x) := bmul (lowGeometry36W_hz0 hx hc) (lowGeometry36W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (114693192713327 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry36W_hz17 hx hc) (lowGeometry36W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (5354745388749287 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry36W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (16064236166247861 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry36W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (16064236166247861 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry36W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry36W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (478 / 125) (957 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry36W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry36W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (42798341089345977 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry36W_hz22 hx hc) (lowGeometry36W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry36W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry36W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry36W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry36W_hz26 hx hc) (lowGeometry36W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry36W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (44989179699123213 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry36W_hz24 hx hc) (lowGeometry36W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (266064236166247861 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry36W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (1132642844267662661 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry36W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (1043 / 2000) (59123956470771991 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry36W_hz2 hx hc) (lowGeometry36W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (1043 / 2000) (636228744406843123 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry36W_hz33 hx hc) (lowGeometry36W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (1043 / 2000) (636228744406843123 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry36W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry36W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (233935763833752139 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry36W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (218903766401924221 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry36W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (18265330268576557 / 40000000000000000) (261 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry36W_hz2 hx hc) (lowGeometry36W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (51455509626911339 / 125000000000000000) (261 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry36W_hz38 hx hc) (lowGeometry36W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (51455509626911339 / 125000000000000000) (261 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry36W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry36W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (239 / 500) (957 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (368429303 / 1000000000) (718823031 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (22980423 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry36W_hz12 hx hc).2
  have hrp := (lowGeometry36W_hz16 hx hc).2
  have hbn := (lowGeometry36W_hz21 hx hc).2
  have hlo := (lowGeometry36W_hz40 hx hc).1
  have hhi := (lowGeometry36W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry36C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (239 / 500) (957 / 2000) θ := hc

theorem lowGeometry36C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry36C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (1043 / 2000) (261 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry36C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (249277 / 1000000) (249777 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry36C_hz0 hx hc) (lowGeometry36C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (249777 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry36C_hz3 hx hc) (lowGeometry36C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (1396919042929833 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry36C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (32185014749103353 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry36C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (239 / 250) (957 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry36C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry36C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry36C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (29901464617138741 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry36C_hz7 hx hc) (lowGeometry36C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (31043239683121047 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry36C_hz6 hx hc) (lowGeometry36C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (31043239683121047 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry36C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry36C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (186659 / 25000) (747417 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry36C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (747417 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry36C_hz13 hx hc) (lowGeometry36C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (31510375308121047 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry36C_hz12 hx hc) (lowGeometry36C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (31510375308121047 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry36C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry36C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (957 / 16000000) (θ * x) := bmul (lowGeometry36C_hz0 hx hc) (lowGeometry36C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (114693192713327 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry36C_hz17 hx hc) (lowGeometry36C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (5354745388749287 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry36C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (15421666719597947 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry36C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (15421666719597947 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry36C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry36C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (78153 / 50000) (312939 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry36C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry36C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (17493821920270169 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry36C_hz22 hx hc) (lowGeometry36C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry36C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry36C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry36C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry36C_hz26 hx hc) (lowGeometry36C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry36C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 0 (3609738985779103 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry36C_hz24 hx hc) (lowGeometry36C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (515421666719597947 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry36C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B 1 (132829747262004151 / 125000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry36C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (1043 / 2000) (110939404913225867 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry36C_hz2 hx hc) (lowGeometry36C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (1043 / 2000) (11454914389900497 / 20000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry36C_hz33 hx hc) (lowGeometry36C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (1043 / 2000) (11454914389900497 / 20000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry36C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry36C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (484578333280402053 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry36C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (939264644339249631 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry36C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (244913256011459341 / 500000000000000000) (261 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry36C_hz2 hx hc) (lowGeometry36C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (471777817094023167 / 1000000000000000000) (261 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry36C_hz38 hx hc) (lowGeometry36C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry36C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (239 / 500) (957 / 2000) θ) : B (471777817094023167 / 1000000000000000000) (261 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry36C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry36C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (239 / 500) (957 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (221904331 / 500000000) (610659413 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (776081 / 12500000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry36C_hz12 hx hc).2
  have hrp := (lowGeometry36C_hz16 hx hc).2
  have hbn := (lowGeometry36C_hz21 hx hc).2
  have hlo := (lowGeometry36C_hz40 hx hc).1
  have hhi := (lowGeometry36C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry37W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (957 / 2000) (479 / 1000) θ := hc

theorem lowGeometry37W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry37W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (521 / 1000) (1043 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry37W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (498597 / 2000000) (499597 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry37W_hz0 hx hc) (lowGeometry37W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (499597 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry37W_hz3 hx hc) (lowGeometry37W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (1396979162783039 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry37W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (4190937488349117 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry37W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (957 / 1000) (479 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry37W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry37W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry37W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (479 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry37W_hz7 hx hc) (lowGeometry37W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7184687488349117 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry37W_hz6 hx hc) (lowGeometry37W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7184687488349117 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry37W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry37W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (957 / 50) (479 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry37W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (479 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry37W_hz13 hx hc) (lowGeometry37W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7334374988349117 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry37W_hz12 hx hc) (lowGeometry37W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7334374988349117 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry37W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry37W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (479 / 8000000) (θ * x) := bmul (lowGeometry37W_hz0 hx hc) (lowGeometry37W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (114923224568139 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry37W_hz17 hx hc) (lowGeometry37W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (5360112512068637 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry37W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (16080337536205911 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry37W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (16080337536205911 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry37W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry37W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (957 / 250) (479 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry37W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry37W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (42843062448895973 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry37W_hz22 hx hc) (lowGeometry37W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry37W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry37W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry37W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry37W_hz26 hx hc) (lowGeometry37W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry37W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (22518095168108693 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry37W_hz24 hx hc) (lowGeometry37W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (266080337536205911 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry37W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (1132779936374100293 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry37W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (521 / 1000) (590744736819093303 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry37W_hz2 hx hc) (lowGeometry37W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (521 / 1000) (635780927155310689 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry37W_hz33 hx hc) (lowGeometry37W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (521 / 1000) (635780927155310689 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry37W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry37W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (233919662463794089 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry37W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (218873633948701429 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry37W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (228066326574546889 / 500000000000000000) (1043 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry37W_hz2 hx hc) (lowGeometry37W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (51387057851609549 / 125000000000000000) (1043 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry37W_hz38 hx hc) (lowGeometry37W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (51387057851609549 / 125000000000000000) (1043 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry37W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry37W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (957 / 2000) (479 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (18396047 / 50000000) (718360001 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (22991 / 200000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry37W_hz12 hx hc).2
  have hrp := (lowGeometry37W_hz16 hx hc).2
  have hbn := (lowGeometry37W_hz21 hx hc).2
  have hlo := (lowGeometry37W_hz40 hx hc).1
  have hhi := (lowGeometry37W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry37C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (957 / 2000) (479 / 1000) θ := hc

theorem lowGeometry37C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry37C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (521 / 1000) (1043 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry37C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (498597 / 2000000) (499597 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry37C_hz0 hx hc) (lowGeometry37C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (499597 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry37C_hz3 hx hc) (lowGeometry37C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (1396979162783039 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry37C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (32186399910521219 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry37C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (957 / 1000) (479 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry37C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry37C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry37C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (29932709616738677 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry37C_hz7 hx hc) (lowGeometry37C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7764888690907487 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry37C_hz6 hx hc) (lowGeometry37C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7764888690907487 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry37C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry37C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (747417 / 100000) (374099 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry37C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (374099 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry37C_hz13 hx hc) (lowGeometry37C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7881794628407487 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry37C_hz12 hx hc) (lowGeometry37C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7881794628407487 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry37C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry37C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (479 / 8000000) (θ * x) := bmul (lowGeometry37C_hz0 hx hc) (lowGeometry37C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (114923224568139 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry37C_hz17 hx hc) (lowGeometry37C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (5360112512068637 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry37C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (617484961390307 / 20000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry37C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (617484961390307 / 20000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry37C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry37C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (312939 / 200000) (156633 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry37C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry37C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (17512101775986229 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry37C_hz22 hx hc) (lowGeometry37C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry37C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry37C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry37C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry37C_hz26 hx hc) (lowGeometry37C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry37C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 0 (18067554589218289 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry37C_hz24 hx hc) (lowGeometry37C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (20617484961390307 / 20000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry37C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B 1 (1062701715332888673 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry37C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (521 / 1000) (554198944546101443 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry37C_hz2 hx hc) (lowGeometry37C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (521 / 1000) (143066624783829933 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry37C_hz33 hx hc) (lowGeometry37C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (521 / 1000) (143066624783829933 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry37C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry37C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (19382515038609693 / 20000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry37C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (117400590381853409 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry37C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (30582853794472813 / 62500000000000000) (1043 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry37C_hz2 hx hc) (lowGeometry37C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (471258106122346719 / 1000000000000000000) (1043 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry37C_hz38 hx hc) (lowGeometry37C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry37C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (957 / 2000) (479 / 1000) θ) : B (471258106122346719 / 1000000000000000000) (1043 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry37C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry37C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (957 / 2000) (479 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (443305747 / 1000000000) (305084849 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (6211911 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry37C_hz12 hx hc).2
  have hrp := (lowGeometry37C_hz16 hx hc).2
  have hbn := (lowGeometry37C_hz21 hx hc).2
  have hlo := (lowGeometry37C_hz40 hx hc).1
  have hhi := (lowGeometry37C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry38W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (479 / 1000) (959 / 2000) θ := hc

theorem lowGeometry38W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry38W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (1041 / 2000) (521 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry38W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (498639 / 2000000) (499639 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry38W_hz0 hx hc) (lowGeometry38W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (499639 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry38W_hz3 hx hc) (lowGeometry38W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1397037882002489 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry38W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (4191113646007467 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry38W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (479 / 500) (959 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry38W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry38W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry38W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (959 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry38W_hz7 hx hc) (lowGeometry38W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (7187988646007467 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry38W_hz6 hx hc) (lowGeometry38W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (7187988646007467 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry38W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry38W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (479 / 25) (959 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry38W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (959 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry38W_hz13 hx hc) (lowGeometry38W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (7337832396007467 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry38W_hz12 hx hc) (lowGeometry38W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (7337832396007467 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry38W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry38W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (959 / 16000000) (θ * x) := bmul (lowGeometry38W_hz0 hx hc) (lowGeometry38W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (23030739673391 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry38W_hz17 hx hc) (lowGeometry38W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (107309691252447 / 10000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry38W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (321929073757341 / 5000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry38W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (321929073757341 / 5000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry38W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry38W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (479 / 125) (959 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry38W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry38W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (42887783808445969 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry38W_hz22 hx hc) (lowGeometry38W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry38W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry38W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry38W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry38W_hz26 hx hc) (lowGeometry38W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry38W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (45083200973311559 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry38W_hz24 hx hc) (lowGeometry38W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (5321929073757341 / 5000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry38W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (1132917162644146781 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry38W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (1041 / 2000) (590249841737600473 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry38W_hz2 hx hc) (lowGeometry38W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (1041 / 2000) (19854157584716001 / 31250000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry38W_hz33 hx hc) (lowGeometry38W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (1041 / 2000) (19854157584716001 / 31250000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry38W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry38W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (4678070926242659 / 5000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry38W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (43768695181913699 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry38W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (227816058421860803 / 500000000000000000) (521 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry38W_hz2 hx hc) (lowGeometry38W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (410548915870410047 / 1000000000000000000) (521 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry38W_hz38 hx hc) (lowGeometry38W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (410548915870410047 / 1000000000000000000) (521 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry38W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry38W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (479 / 1000) (959 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (367412709 / 1000000000) (358948393 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (115007819 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry38W_hz12 hx hc).2
  have hrp := (lowGeometry38W_hz16 hx hc).2
  have hbn := (lowGeometry38W_hz21 hx hc).2
  have hlo := (lowGeometry38W_hz40 hx hc).1
  have hhi := (lowGeometry38W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry38C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (479 / 1000) (959 / 2000) θ := hc

theorem lowGeometry38C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry38C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (1041 / 2000) (521 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry38C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (498639 / 2000000) (499639 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry38C_hz0 hx hc) (lowGeometry38C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (499639 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry38C_hz3 hx hc) (lowGeometry38C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1397037882002489 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry38C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (32187752801337347 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry38C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (479 / 500) (959 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry38C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry38C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry38C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (29963954616338613 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry38C_hz7 hx hc) (lowGeometry38C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1553792685441899 / 25000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry38C_hz6 hx hc) (lowGeometry38C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1553792685441899 / 25000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry38C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry38C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (374099 / 50000) (748979 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry38C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (748979 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry38C_hz13 hx hc) (lowGeometry38C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1577198279191899 / 25000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry38C_hz12 hx hc) (lowGeometry38C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1577198279191899 / 25000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry38C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry38C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (959 / 16000000) (θ * x) := bmul (lowGeometry38C_hz0 hx hc) (lowGeometry38C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (23030739673391 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry38C_hz17 hx hc) (lowGeometry38C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (107309691252447 / 10000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry38C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (965787221272023 / 31250000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry38C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (965787221272023 / 31250000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry38C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry38C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (156633 / 100000) (313593 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry38C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry38C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (1753038163170229 / 100000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry38C_hz22 hx hc) (lowGeometry38C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry38C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry38C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry38C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry38C_hz26 hx hc) (lowGeometry38C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry38C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 0 (2260801781192633 / 125000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry38C_hz24 hx hc) (lowGeometry38C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (32215787221272023 / 31250000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry38C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B 1 (132845689124643043 / 125000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry38C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (1041 / 2000) (138425208067878051 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry38C_hz2 hx hc) (lowGeometry38C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (1041 / 2000) (142946811630263317 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry38C_hz33 hx hc) (lowGeometry38C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (1041 / 2000) (142946811630263317 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry38C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry38C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (30284212778727977 / 31250000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry38C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (939144748674325399 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry38C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (48882484168498637 / 100000000000000000) (521 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry38C_hz2 hx hc) (lowGeometry38C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (235369213717722653 / 500000000000000000) (521 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry38C_hz38 hx hc) (lowGeometry38C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry38C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (479 / 1000) (959 / 2000) θ) : B (235369213717722653 / 500000000000000000) (521 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry38C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry38C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (479 / 1000) (959 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (110700727 / 250000000) (609679893 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15537927 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry38C_hz12 hx hc).2
  have hrp := (lowGeometry38C_hz16 hx hc).2
  have hbn := (lowGeometry38C_hz21 hx hc).2
  have hlo := (lowGeometry38C_hz40 hx hc).1
  have hhi := (lowGeometry38C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry39W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (959 / 2000) (12 / 25) θ := hc

theorem lowGeometry39W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry39W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (13 / 25) (1041 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry39W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (12467 / 50000) (3123 / 12500) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry39W_hz0 hx hc) (lowGeometry39W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (3123 / 100000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry39W_hz3 hx hc) (lowGeometry39W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (1397095200764787 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry39W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (4191285602294361 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry39W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (959 / 1000) (24 / 25) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry39W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry39W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry39W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (6 / 125) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry39W_hz7 hx hc) (lowGeometry39W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (7191285602294361 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry39W_hz6 hx hc) (lowGeometry39W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (7191285602294361 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry39W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry39W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (959 / 50) (96 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry39W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (3 / 1250) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry39W_hz13 hx hc) (lowGeometry39W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (7341285602294361 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry39W_hz12 hx hc) (lowGeometry39W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (7341285602294361 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry39W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry39W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (3 / 50000) (θ * x) := bmul (lowGeometry39W_hz0 hx hc) (lowGeometry39W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (14423076923077 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry39W_hz17 hx hc) (lowGeometry39W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (5370861555295761 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry39W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (16112584665887283 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry39W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (16112584665887283 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry39W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry39W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (959 / 250) (96 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry39W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry39W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (8586501033599193 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry39W_hz22 hx hc) (lowGeometry39W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry39W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry39W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry39W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry39W_hz26 hx hc) (lowGeometry39W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry39W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (11282552902601433 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry39W_hz24 hx hc) (lowGeometry39W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (266112584665887283 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry39W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (1133054523480944441 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry39W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (13 / 25) (294877439735915791 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry39W_hz2 hx hc) (lowGeometry39W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (13 / 25) (317442545541118657 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry39W_hz33 hx hc) (lowGeometry39W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (13 / 25) (317442545541118657 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry39W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry39W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (233887415334112717 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry39W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (109406646103343489 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry39W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (227565823894954457 / 500000000000000000) (1041 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry39W_hz2 hx hc) (lowGeometry39W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (205000718089751591 / 500000000000000000) (1041 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry39W_hz38 hx hc) (lowGeometry39W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (205000718089751591 / 500000000000000000) (1041 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry39W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry39W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (959 / 2000) (12 / 25) θ) :
    OverlapGuard n θ lowWideWindow (366904611 / 1000000000) (358716693 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (11506057 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry39W_hz12 hx hc).2
  have hrp := (lowGeometry39W_hz16 hx hc).2
  have hbn := (lowGeometry39W_hz21 hx hc).2
  have hlo := (lowGeometry39W_hz40 hx hc).1
  have hhi := (lowGeometry39W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry39C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (959 / 2000) (12 / 25) θ := hc

theorem lowGeometry39C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry39C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (13 / 25) (1041 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry39C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (12467 / 50000) (3123 / 12500) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry39C_hz0 hx hc) (lowGeometry39C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (3123 / 100000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry39C_hz3 hx hc) (lowGeometry39C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (1397095200764787 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry39C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (32189073425620693 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry39C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (959 / 1000) (24 / 25) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry39C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry39C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry39C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (29995199615938549 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry39C_hz7 hx hc) (lowGeometry39C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (31092136520779621 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry39C_hz6 hx hc) (lowGeometry39C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (31092136520779621 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry39C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry39C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (748979 / 100000) (4686 / 625) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry39C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (2343 / 2500000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry39C_hz13 hx hc) (lowGeometry39C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (31560736520779621 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry39C_hz12 hx hc) (lowGeometry39C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (31560736520779621 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry39C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry39C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (3 / 50000) (θ * x) := bmul (lowGeometry39C_hz0 hx hc) (lowGeometry39C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (14423076923077 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry39C_hz17 hx hc) (lowGeometry39C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (5370861555295761 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry39C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (966755079953237 / 31250000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry39C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (966755079953237 / 31250000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry39C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry39C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (313593 / 200000) (981 / 625) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry39C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry39C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (17548661487418351 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry39C_hz22 hx hc) (lowGeometry39C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry39C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry39C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry39C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry39C_hz26 hx hc) (lowGeometry39C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry39C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 0 (18105273909863839 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry39C_hz24 hx hc) (lowGeometry39C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (32216755079953237 / 31250000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry39C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B 1 (66426835704428333 / 62500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry39C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (13 / 25) (276601343873239579 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry39C_hz2 hx hc) (lowGeometry39C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (13 / 25) (571307961656342997 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry39C_hz33 hx hc) (lowGeometry39C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (13 / 25) (571307961656342997 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry39C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry39C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (30283244920046763 / 31250000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry39C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (939084721036838991 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry39C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (19532962197566251 / 40000000000000000) (1041 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry39C_hz2 hx hc) (lowGeometry39C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (117554695257323109 / 250000000000000000) (1041 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry39C_hz38 hx hc) (lowGeometry39C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry39C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (959 / 2000) (12 / 25) θ) : B (117554695257323109 / 250000000000000000) (1041 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry39C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry39C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (959 / 2000) (12 / 25) θ) :
    OverlapGuard n θ lowCoreWindow (27643759 / 62500000) (609189999 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31092137 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry39C_hz12 hx hc).2
  have hrp := (lowGeometry39C_hz16 hx hc).2
  have hbn := (lowGeometry39C_hz21 hx hc).2
  have hlo := (lowGeometry39C_hz40 hx hc).1
  have hhi := (lowGeometry39C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry40W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (12 / 25) (961 / 2000) θ := hc

theorem lowGeometry40W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry40W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (1039 / 2000) (13 / 25) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (3117 / 12500) (12493 / 50000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry40W_hz0 hx hc) (lowGeometry40W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (12493 / 400000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry40W_hz3 hx hc) (lowGeometry40W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (174643889905287 / 31250000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry40W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (523931669715861 / 7812500000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry40W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (24 / 25) (961 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry40W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry40W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (961 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry40W_hz7 hx hc) (lowGeometry40W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (899322294715861 / 7812500000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry40W_hz6 hx hc) (lowGeometry40W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (899322294715861 / 7812500000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry40W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry40W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (96 / 5) (961 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry40W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (961 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry40W_hz13 hx hc) (lowGeometry40W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (918091825965861 / 7812500000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry40W_hz12 hx hc) (lowGeometry40W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (918091825965861 / 7812500000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry40W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry40W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (961 / 16000000) (θ * x) := bmul (lowGeometry40W_hz0 hx hc) (lowGeometry40W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (115615976900867 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry40W_hz17 hx hc) (lowGeometry40W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (2150497402006029 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry40W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (6451492206018087 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry40W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (6451492206018087 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry40W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry40W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (96 / 25) (961 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry40W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry40W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (1074430663188649 / 25000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry40W_hz22 hx hc) (lowGeometry40W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry40W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry40W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry40W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry40W_hz26 hx hc) (lowGeometry40W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry40W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (352947048808593 / 7812500000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry40W_hz24 hx hc) (lowGeometry40W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (106451492206018087 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry40W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (1133192019288792953 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry40W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (1039 / 2000) (36828740626885771 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry40W_hz2 hx hc) (lowGeometry40W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (1039 / 2000) (7930463403470903 / 12500000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry40W_hz33 hx hc) (lowGeometry40W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (1039 / 2000) (7930463403470903 / 12500000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry40W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry40W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (93548507793981913 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry40W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (27347885345252171 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry40W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (45463124597947209 / 100000000000000000) (13 / 25) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry40W_hz2 hx hc) (lowGeometry40W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (204727011865986093 / 500000000000000000) (13 / 25) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry40W_hz38 hx hc) (lowGeometry40W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (204727011865986093 / 500000000000000000) (13 / 25) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry40W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry40W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (12 / 25) (961 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (73279329 / 200000000) (716969799 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (57556627 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry40W_hz12 hx hc).2
  have hrp := (lowGeometry40W_hz16 hx hc).2
  have hbn := (lowGeometry40W_hz21 hx hc).2
  have hlo := (lowGeometry40W_hz40 hx hc).1
  have hhi := (lowGeometry40W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry40C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (12 / 25) (961 / 2000) θ := hc

theorem lowGeometry40C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry40C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (1039 / 2000) (13 / 25) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (3117 / 12500) (12493 / 50000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry40C_hz0 hx hc) (lowGeometry40C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (12493 / 400000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry40C_hz3 hx hc) (lowGeometry40C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (174643889905287 / 31250000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry40C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (12876144714937 / 400000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry40C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (24 / 25) (961 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry40C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry40C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (6005288923107697 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry40C_hz7 hx hc) (lowGeometry40C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (12443361280576197 / 200000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry40C_hz6 hx hc) (lowGeometry40C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (12443361280576197 / 200000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry40C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry40C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (4686 / 625) (750541 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry40C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (750541 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry40C_hz13 hx hc) (lowGeometry40C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (12630996530576197 / 200000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry40C_hz12 hx hc) (lowGeometry40C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (12630996530576197 / 200000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry40C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry40C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (961 / 16000000) (θ * x) := bmul (lowGeometry40C_hz0 hx hc) (lowGeometry40C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (115615976900867 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry40C_hz17 hx hc) (lowGeometry40C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (2150497402006029 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry40C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (15483581294443409 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry40C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (15483581294443409 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry40C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry40C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (981 / 625) (314247 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry40C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry40C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (4391735335783603 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry40C_hz22 hx hc) (lowGeometry40C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry40C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry40C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry40C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry40C_hz26 hx hc) (lowGeometry40C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry40C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 0 (9062066785093307 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry40C_hz24 hx hc) (lowGeometry40C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (515483581294443409 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry40C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B 1 (265723322584145047 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry40C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (1039 / 2000) (276352255487510849 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry40C_hz2 hx hc) (lowGeometry40C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (1039 / 2000) (71353580568151039 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry40C_hz33 hx hc) (lowGeometry40C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (1039 / 2000) (71353580568151039 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry40C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry40C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (484516418705556591 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry40C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (187804927996206583 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry40C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (487823300470146599 / 1000000000000000000) (13 / 25) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry40C_hz2 hx hc) (lowGeometry40C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (93939833379991997 / 200000000000000000) (13 / 25) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry40C_hz38 hx hc) (lowGeometry40C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry40C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (961 / 2000) θ) : B (93939833379991997 / 200000000000000000) (13 / 25) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry40C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry40C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (12 / 25) (961 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (27612341 / 62500000) (38043751 / 62500000) ∧ radiusMinus n θ lowCoreWindow ≤ (62216807 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry40C_hz12 hx hc).2
  have hrp := (lowGeometry40C_hz16 hx hc).2
  have hbn := (lowGeometry40C_hz21 hx hc).2
  have hlo := (lowGeometry40C_hz40 hx hc).1
  have hhi := (lowGeometry40C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry41W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (961 / 2000) (481 / 1000) θ := hc

theorem lowGeometry41W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry41W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (519 / 1000) (1039 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry41W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (498759 / 2000000) (499759 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry41W_hz0 hx hc) (lowGeometry41W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (499759 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry41W_hz3 hx hc) (lowGeometry41W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (1117764510082513 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry41W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (3353293530247539 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry41W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (961 / 1000) (481 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry41W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry41W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry41W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (481 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry41W_hz7 hx hc) (lowGeometry41W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (5758293530247539 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry41W_hz6 hx hc) (lowGeometry41W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (5758293530247539 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry41W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry41W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (961 / 50) (481 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry41W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (481 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry41W_hz13 hx hc) (lowGeometry41W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (5878543530247539 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry41W_hz12 hx hc) (lowGeometry41W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (5878543530247539 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry41W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry41W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (481 / 8000000) (θ * x) := bmul (lowGeometry41W_hz0 hx hc) (lowGeometry41W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (57923892100193 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry41W_hz17 hx hc) (lowGeometry41W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (672703803343461 / 62500000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry41W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (2018111410030383 / 31250000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry41W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (2018111410030383 / 31250000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry41W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry41W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (961 / 250) (481 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry41W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry41W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (10755486971773989 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry41W_hz22 hx hc) (lowGeometry41W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry41W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry41W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry41W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry41W_hz26 hx hc) (lowGeometry41W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry41W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (11306058221148519 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry41W_hz24 hx hc) (lowGeometry41W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (33268111410030383 / 31250000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry41W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (1133329650473158409 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry41W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (519 / 1000) (294382376710402897 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry41W_hz2 hx hc) (lowGeometry41W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (519 / 1000) (63398898630539987 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry41W_hz33 hx hc) (lowGeometry41W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (519 / 1000) (63398898630539987 / 100000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry41W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry41W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (29231888589969617 / 31250000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry41W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (109376423748658673 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry41W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (45413091140443081 / 100000000000000000) (1039 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry41W_hz2 hx hc) (lowGeometry41W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (204453339259918367 / 500000000000000000) (1039 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry41W_hz38 hx hc) (lowGeometry41W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (204453339259918367 / 500000000000000000) (1039 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry41W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry41W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (961 / 2000) (481 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (91472203 / 250000000) (716506027 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (115165871 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry41W_hz12 hx hc).2
  have hrp := (lowGeometry41W_hz16 hx hc).2
  have hbn := (lowGeometry41W_hz21 hx hc).2
  have hlo := (lowGeometry41W_hz40 hx hc).1
  have hhi := (lowGeometry41W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry41C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (961 / 2000) (481 / 1000) θ := hc

theorem lowGeometry41C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry41C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (519 / 1000) (1039 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry41C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (498759 / 2000000) (499759 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry41C_hz0 hx hc) (lowGeometry41C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (499759 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry41C_hz3 hx hc) (lowGeometry41C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (1117764510082513 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry41C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (257532943123011 / 8000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry41C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (961 / 1000) (481 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry41C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry41C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry41C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (30057689615138421 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry41C_hz7 hx hc) (lowGeometry41C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (15562326876378699 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry41C_hz6 hx hc) (lowGeometry41C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (15562326876378699 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry41C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry41C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (750541 / 100000) (375661 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry41C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (375661 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry41C_hz13 hx hc) (lowGeometry41C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (15797115001378699 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry41C_hz12 hx hc) (lowGeometry41C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (15797115001378699 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry41C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry41C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (481 / 8000000) (θ * x) := bmul (lowGeometry41C_hz0 hx hc) (lowGeometry41C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (57923892100193 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry41C_hz17 hx hc) (lowGeometry41C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (672703803343461 / 62500000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry41C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (30998191258066683 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry41C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (30998191258066683 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry41C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry41C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (314247 / 200000) (157287 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry41C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry41C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (2198152649856309 / 125000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry41C_hz22 hx hc) (lowGeometry41C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry41C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry41C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry41C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry41C_hz26 hx hc) (lowGeometry41C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry41C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 0 (4535748307627347 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry41C_hz24 hx hc) (lowGeometry41C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (1030998191258066683 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry41C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B 1 (132869658797175631 / 125000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry41C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (519 / 1000) (552206301961061923 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry41C_hz2 hx hc) (lowGeometry41C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (519 / 1000) (570349295191571311 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry41C_hz33 hx hc) (lowGeometry41C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (519 / 1000) (570349295191571311 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry41C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry41C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (969001808741933317 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry41C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (187792901069027663 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry41C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (97464515654825357 / 200000000000000000) (1039 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry41C_hz2 hx hc) (lowGeometry41C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (469179585043617397 / 1000000000000000000) (1039 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry41C_hz38 hx hc) (lowGeometry41C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry41C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (961 / 2000) (481 / 1000) θ) : B (469179585043617397 / 1000000000000000000) (1039 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry41C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry41C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (961 / 2000) (481 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (441294843 / 1000000000) (608209943 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15562327 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry41C_hz12 hx hc).2
  have hrp := (lowGeometry41C_hz16 hx hc).2
  have hbn := (lowGeometry41C_hz21 hx hc).2
  have hlo := (lowGeometry41C_hz40 hx hc).1
  have hhi := (lowGeometry41C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry42W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (481 / 1000) (963 / 2000) θ := hc

theorem lowGeometry42W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry42W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (1037 / 2000) (519 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry42W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (498797 / 2000000) (499797 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry42W_hz0 hx hc) (lowGeometry42W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (499797 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry42W_hz3 hx hc) (lowGeometry42W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (5589035024044849 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry42W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (16767105072134547 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry42W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (481 / 500) (963 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry42W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry42W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry42W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (963 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry42W_hz7 hx hc) (lowGeometry42W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (28804605072134547 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry42W_hz6 hx hc) (lowGeometry42W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (28804605072134547 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry42W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry42W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (481 / 25) (963 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry42W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (963 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry42W_hz13 hx hc) (lowGeometry42W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (29406480072134547 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry42W_hz12 hx hc) (lowGeometry42W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (29406480072134547 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry42W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry42W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (963 / 16000000) (θ * x) := bmul (lowGeometry42W_hz0 hx hc) (lowGeometry42W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (116080038572807 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry42W_hz17 hx hc) (lowGeometry42W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (2693511167751201 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry42W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (8080533503253603 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry42W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (8080533503253603 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry42W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry42W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (481 / 125) (963 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry42W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry42W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (672916706978843 / 15625000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry42W_hz22 hx hc) (lowGeometry42W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry42W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry42W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry42W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry42W_hz26 hx hc) (lowGeometry42W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry42W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (45271243521688249 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry42W_hz24 hx hc) (lowGeometry42W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (133080533503253603 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry42W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (1133467417440678701 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry42W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (1037 / 2000) (294134794825856123 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry42W_hz2 hx hc) (lowGeometry42W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (1037 / 2000) (126708166634680099 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry42W_hz33 hx hc) (lowGeometry42W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (1037 / 2000) (126708166634680099 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry42W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry42W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (116919466496746397 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry42W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (218722586334140851 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry42W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (113407661014252031 / 250000000000000000) (519 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry42W_hz2 hx hc) (lowGeometry42W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (3266875204282559 / 8000000000000000) (519 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry42W_hz38 hx hc) (lowGeometry42W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (3266875204282559 / 8000000000000000) (519 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry42W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry42W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (481 / 1000) (963 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (365381111 / 1000000000) (71604207 / 100000000) ∧ radiusMinus n θ lowWideWindow ≤ (115218421 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry42W_hz12 hx hc).2
  have hrp := (lowGeometry42W_hz16 hx hc).2
  have hbn := (lowGeometry42W_hz21 hx hc).2
  have hlo := (lowGeometry42W_hz40 hx hc).1
  have hhi := (lowGeometry42W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry42C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (481 / 1000) (963 / 2000) θ := hc

theorem lowGeometry42C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry42C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (1037 / 2000) (519 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry42C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (498797 / 2000000) (499797 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry42C_hz0 hx hc) (lowGeometry42C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (499797 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry42C_hz3 hx hc) (lowGeometry42C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (5589035024044849 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry42C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (32192841738498331 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry42C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (481 / 500) (963 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry42C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry42C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry42C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (30088934614738357 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry42C_hz7 hx hc) (lowGeometry42C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (3892611022077293 / 62500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry42C_hz6 hx hc) (lowGeometry42C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (3892611022077293 / 62500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry42C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry42C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (375661 / 50000) (752103 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry42C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (752103 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry42C_hz13 hx hc) (lowGeometry42C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (3951369068952293 / 62500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry42C_hz12 hx hc) (lowGeometry42C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (3951369068952293 / 62500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry42C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry42C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (963 / 16000000) (θ * x) := bmul (lowGeometry42C_hz0 hx hc) (lowGeometry42C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (116080038572807 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry42C_hz17 hx hc) (lowGeometry42C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (2693511167751201 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry42C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (7757312163123459 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry42C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (7757312163123459 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry42C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry42C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (157287 / 100000) (314901 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry42C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry42C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (17603501054566533 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry42C_hz22 hx hc) (lowGeometry42C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry42C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry42C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry42C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry42C_hz26 hx hc) (lowGeometry42C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry42C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 0 (18161852890832163 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry42C_hz24 hx hc) (lowGeometry42C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (257757312163123459 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry42C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B 1 (1063021311576925963 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry42C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (1037 / 2000) (22068322428336983 / 40000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry42C_hz2 hx hc) (lowGeometry42C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (1037 / 2000) (284934956799628369 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry42C_hz33 hx hc) (lowGeometry42C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (1037 / 2000) (284934956799628369 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry42C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry42C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (242242687836876541 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry42C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (469452158483475309 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry42C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (97364377669472779 / 200000000000000000) (519 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry42C_hz2 hx hc) (lowGeometry42C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (117165008864132933 / 250000000000000000) (519 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry42C_hz38 hx hc) (lowGeometry42C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry42C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (481 / 1000) (963 / 2000) θ) : B (117165008864132933 / 250000000000000000) (519 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry42C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry42C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (481 / 1000) (963 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (220396153 / 500000000) (303859891 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62281777 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry42C_hz12 hx hc).2
  have hrp := (lowGeometry42C_hz16 hx hc).2
  have hbn := (lowGeometry42C_hz21 hx hc).2
  have hlo := (lowGeometry42C_hz40 hx hc).1
  have hhi := (lowGeometry42C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry43W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (963 / 2000) (241 / 500) θ := hc

theorem lowGeometry43W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry43W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (259 / 500) (1037 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry43W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (249417 / 1000000) (249917 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry43W_hz0 hx hc) (lowGeometry43W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (249917 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry43W_hz3 hx hc) (lowGeometry43W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (5589241898504663 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry43W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (16767725695513989 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry43W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (963 / 1000) (241 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry43W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry43W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry43W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (241 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry43W_hz7 hx hc) (lowGeometry43W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (28817725695513989 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry43W_hz6 hx hc) (lowGeometry43W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (28817725695513989 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry43W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry43W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (963 / 50) (482 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry43W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (241 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry43W_hz13 hx hc) (lowGeometry43W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (29420225695513989 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry43W_hz12 hx hc) (lowGeometry43W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (29420225695513989 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry43W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry43W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (241 / 4000000) (θ * x) := bmul (lowGeometry43W_hz0 hx hc) (lowGeometry43W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (58156370656371 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry43W_hz17 hx hc) (lowGeometry43W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1348104811582391 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry43W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (4044314434747173 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry43W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (4044314434747173 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry43W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry43W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (963 / 250) (482 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry43W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry43W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (10777847651548987 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry43W_hz22 hx hc) (lowGeometry43W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry43W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry43W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry43W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry43W_hz26 hx hc) (lowGeometry43W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry43W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (22659127079391211 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry43W_hz24 hx hc) (lowGeometry43W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (66544314434747173 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry43W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (1133605320599168249 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry43W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (259 / 500) (293887179365334369 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry43W_hz2 hx hc) (lowGeometry43W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (259 / 500) (15827315322236279 / 25000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry43W_hz33 hx hc) (lowGeometry43W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (259 / 500) (15827315322236279 / 25000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry43W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry43W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (58455685565252827 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry43W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (109346149596918647 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry43W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (453130443929630873 / 1000000000000000000) (1037 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry43W_hz2 hx hc) (lowGeometry43W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (407812189770848451 / 1000000000000000000) (1037 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry43W_hz38 hx hc) (lowGeometry43W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (407812189770848451 / 1000000000000000000) (1037 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry43W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry43W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (963 / 2000) (241 / 500) θ) :
    OverlapGuard n θ lowWideWindow (364873541 / 1000000000) (715577927 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (115270903 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry43W_hz12 hx hc).2
  have hrp := (lowGeometry43W_hz16 hx hc).2
  have hbn := (lowGeometry43W_hz21 hx hc).2
  have hlo := (lowGeometry43W_hz40 hx hc).1
  have hhi := (lowGeometry43W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry43C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (963 / 2000) (241 / 500) θ := hc

theorem lowGeometry43C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry43C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (259 / 500) (1037 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry43C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (249417 / 1000000) (249917 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry43C_hz0 hx hc) (lowGeometry43C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (249917 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry43C_hz3 hx hc) (lowGeometry43C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (5589241898504663 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry43C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (32194033335386859 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry43C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (963 / 1000) (241 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry43C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry43C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry43C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (30120179614338293 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry43C_hz7 hx hc) (lowGeometry43C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1947319154678911 / 31250000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry43C_hz6 hx hc) (lowGeometry43C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1947319154678911 / 31250000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry43C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry43C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (752103 / 100000) (188221 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry43C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (188221 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry43C_hz13 hx hc) (lowGeometry43C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1976728685928911 / 31250000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry43C_hz12 hx hc) (lowGeometry43C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1976728685928911 / 31250000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry43C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry43C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (241 / 4000000) (θ * x) := bmul (lowGeometry43C_hz0 hx hc) (lowGeometry43C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (58156370656371 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry43C_hz17 hx hc) (lowGeometry43C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (1348104811582391 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry43C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (31060334858858289 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry43C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (31060334858858289 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry43C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry43C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (314901 / 200000) (78807 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry43C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry43C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (8810890455141297 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry43C_hz22 hx hc) (lowGeometry43C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry43C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry43C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry43C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry43C_hz26 hx hc) (lowGeometry43C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry43C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 0 (9090356275577469 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry43C_hz24 hx hc) (lowGeometry43C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (1031060334858858289 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry43C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B 1 (531542707059630493 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry43C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (259 / 500) (275604893610418411 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry43C_hz2 hx hc) (lowGeometry43C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (259 / 500) (7117381247149897 / 12500000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry43C_hz33 hx hc) (lowGeometry43C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (259 / 500) (7117381247149897 / 12500000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry43C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry43C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (968939665141141711 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry43C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (938844074683827829 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry43C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (97264246137244563 / 200000000000000000) (1037 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry43C_hz2 hx hc) (lowGeometry43C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (468140518135067877 / 1000000000000000000) (1037 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry43C_hz38 hx hc) (lowGeometry43C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry43C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (963 / 2000) (241 / 500) θ) : B (468140518135067877 / 1000000000000000000) (1037 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry43C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry43C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (963 / 2000) (241 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (110072461 / 250000000) (607229531 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62314213 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry43C_hz12 hx hc).2
  have hrp := (lowGeometry43C_hz16 hx hc).2
  have hbn := (lowGeometry43C_hz21 hx hc).2
  have hlo := (lowGeometry43C_hz40 hx hc).1
  have hhi := (lowGeometry43C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry44W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (241 / 500) (193 / 400) θ := hc

theorem lowGeometry44W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry44W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (207 / 400) (259 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry44W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (49887 / 200000) (49987 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry44W_hz0 hx hc) (lowGeometry44W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (49987 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry44W_hz3 hx hc) (lowGeometry44W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (5589443174413709 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry44W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (16768329523241127 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry44W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (241 / 250) (193 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry44W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry44W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry44W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (193 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry44W_hz7 hx hc) (lowGeometry44W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (28830829523241127 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry44W_hz6 hx hc) (lowGeometry44W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (28830829523241127 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry44W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry44W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (482 / 25) (193 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry44W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (193 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry44W_hz13 hx hc) (lowGeometry44W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (29433954523241127 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry44W_hz12 hx hc) (lowGeometry44W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (29433954523241127 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry44W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry44W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (193 / 3200000) (θ * x) := bmul (lowGeometry44W_hz0 hx hc) (lowGeometry44W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (116545893719807 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry44W_hz17 hx hc) (lowGeometry44W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (10795642348642669 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry44W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (32386927045928007 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry44W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (32386927045928007 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry44W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry44W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (482 / 125) (193 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry44W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry44W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (5394513995718243 / 125000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry44W_hz22 hx hc) (lowGeometry44W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry44W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry44W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry44W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry44W_hz26 hx hc) (lowGeometry44W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry44W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (9073052959175319 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry44W_hz24 hx hc) (lowGeometry44W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (532386927045928007 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry44W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (1133743360357625081 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry44W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (207 / 400) (143378676920227 / 244140625000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry44W_hz2 hx hc) (lowGeometry44W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (207 / 400) (632644325461126387 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry44W_hz33 hx hc) (lowGeometry44W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (207 / 400) (632644325461126387 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry44W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry44W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (467613072954071993 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry44W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (13666374124846891 / 15625000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry44W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (452630311014929029 / 1000000000000000000) (259 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry44W_hz2 hx hc) (lowGeometry44W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (203632523109526217 / 500000000000000000) (259 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry44W_hz38 hx hc) (lowGeometry44W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (203632523109526217 / 500000000000000000) (259 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry44W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry44W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (241 / 500) (193 / 400) θ) :
    OverlapGuard n θ lowWideWindow (45545763 / 125000000) (715113599 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (115323319 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry44W_hz12 hx hc).2
  have hrp := (lowGeometry44W_hz16 hx hc).2
  have hbn := (lowGeometry44W_hz21 hx hc).2
  have hlo := (lowGeometry44W_hz40 hx hc).1
  have hhi := (lowGeometry44W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry44C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (241 / 500) (193 / 400) θ := hc

theorem lowGeometry44C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry44C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (207 / 400) (259 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry44C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (49887 / 200000) (49987 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry44C_hz0 hx hc) (lowGeometry44C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (49987 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry44C_hz3 hx hc) (lowGeometry44C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (5589443174413709 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry44C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (8048798171155741 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry44C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (241 / 250) (193 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry44C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry44C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry44C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (30151424613938229 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry44C_hz7 hx hc) (lowGeometry44C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (62346617298561193 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry44C_hz6 hx hc) (lowGeometry44C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (62346617298561193 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry44C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry44C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (188221 / 25000) (150733 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry44C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (150733 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry44C_hz13 hx hc) (lowGeometry44C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (63288698548561193 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry44C_hz12 hx hc) (lowGeometry44C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (63288698548561193 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry44C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry44C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (193 / 3200000) (θ * x) := bmul (lowGeometry44C_hz0 hx hc) (lowGeometry44C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (116545893719807 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry44C_hz17 hx hc) (lowGeometry44C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (10795642348642669 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry44C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (31091449964090887 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry44C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (31091449964090887 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry44C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry44C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (78807 / 50000) (63111 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry44C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry44C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (3528012153199731 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry44C_hz22 hx hc) (lowGeometry44C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry44C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry44C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry44C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry44C_hz26 hx hc) (lowGeometry44C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry44C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 0 (18199572211477713 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry44C_hz24 hx hc) (lowGeometry44C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (1031091449964090887 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry44C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B 1 (531574789094525671 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry44C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (207 / 400) (137677870375482149 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry44C_hz2 hx hc) (lowGeometry44C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (207 / 400) (568911053713406309 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry44C_hz33 hx hc) (lowGeometry44C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (207 / 400) (568911053713406309 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry44C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry44C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (968908550035909113 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry44C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (938783778332687793 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry44C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (121455151321791483 / 250000000000000000) (259 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry44C_hz2 hx hc) (lowGeometry44C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (467621033075688219 / 1000000000000000000) (259 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry44C_hz38 hx hc) (lowGeometry44C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry44C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (241 / 500) (193 / 400) θ) : B (467621033075688219 / 1000000000000000000) (259 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry44C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry44C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (241 / 500) (193 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (439787457 / 1000000000) (60673919 / 100000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31173309 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry44C_hz12 hx hc).2
  have hrp := (lowGeometry44C_hz16 hx hc).2
  have hbn := (lowGeometry44C_hz21 hx hc).2
  have hlo := (lowGeometry44C_hz40 hx hc).1
  have hhi := (lowGeometry44C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry45W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (193 / 400) (483 / 1000) θ := hc

theorem lowGeometry45W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry45W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (517 / 1000) (207 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry45W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (99781 / 400000) (99981 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry45W_hz0 hx hc) (lowGeometry45W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (99981 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry45W_hz3 hx hc) (lowGeometry45W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (279481942618839 / 50000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry45W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (838445827856517 / 12500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry45W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (193 / 200) (483 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry45W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry45W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry45W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (483 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry45W_hz7 hx hc) (lowGeometry45W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1442195827856517 / 12500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry45W_hz6 hx hc) (lowGeometry45W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1442195827856517 / 12500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry45W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry45W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (193 / 10) (483 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry45W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (483 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry45W_hz13 hx hc) (lowGeometry45W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1472383327856517 / 12500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry45W_hz12 hx hc) (lowGeometry45W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1472383327856517 / 12500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry45W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry45W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (483 / 8000000) (θ * x) := bmul (lowGeometry45W_hz0 hx hc) (lowGeometry45W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (116779497098647 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry45W_hz17 hx hc) (lowGeometry45W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1080645626922383 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry45W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (3241936880767149 / 50000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry45W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (3241936880767149 / 50000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry45W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry45W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (193 / 50) (483 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry45W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry45W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (43200833325295939 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry45W_hz22 hx hc) (lowGeometry45W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry45W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry45W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry45W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry45W_hz26 hx hc) (lowGeometry45W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry45W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (45412275432970767 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry45W_hz24 hx hc) (lowGeometry45W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (53241936880767149 / 50000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry45W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (1133881537126237253 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry45W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (517 / 1000) (586783695462827779 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry45W_hz2 hx hc) (lowGeometry45W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (517 / 1000) (316097985447899273 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry45W_hz33 hx hc) (lowGeometry45W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (517 / 1000) (316097985447899273 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry45W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry45W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (46758063119232851 / 50000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry45W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (218631646666216333 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry45W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (28258140331608461 / 62500000000000000) (207 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry45W_hz2 hx hc) (lowGeometry45W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (406717969872764609 / 1000000000000000000) (207 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry45W_hz38 hx hc) (lowGeometry45W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (406717969872764609 / 1000000000000000000) (207 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry45W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry45W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (193 / 400) (483 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (363858799 / 1000000000) (357324543 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (115375667 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry45W_hz12 hx hc).2
  have hrp := (lowGeometry45W_hz16 hx hc).2
  have hbn := (lowGeometry45W_hz21 hx hc).2
  have hlo := (lowGeometry45W_hz40 hx hc).1
  have hhi := (lowGeometry45W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry45C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (193 / 400) (483 / 1000) θ := hc

theorem lowGeometry45C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry45C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (517 / 1000) (207 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry45C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (99781 / 400000) (99981 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry45C_hz0 hx hc) (lowGeometry45C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (99981 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry45C_hz3 hx hc) (lowGeometry45C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (279481942618839 / 50000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry45C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (32196319789690253 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry45C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (193 / 200) (483 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry45C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry45C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry45C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (6036533922707633 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry45C_hz7 hx hc) (lowGeometry45C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (31189494701614209 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry45C_hz6 hx hc) (lowGeometry45C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (31189494701614209 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry45C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry45C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (150733 / 20000) (377223 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry45C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (377223 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry45C_hz13 hx hc) (lowGeometry45C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (31661023451614209 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry45C_hz12 hx hc) (lowGeometry45C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (31661023451614209 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry45C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry45C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (483 / 8000000) (θ * x) := bmul (lowGeometry45C_hz0 hx hc) (lowGeometry45C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (116779497098647 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry45C_hz17 hx hc) (lowGeometry45C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (1080645626922383 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry45C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (31122594055364631 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry45C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (31122594055364631 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry45C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry45C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (63111 / 40000) (157941 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry45C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry45C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (4414585155428679 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry45C_hz22 hx hc) (lowGeometry45C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry45C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry45C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry45C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry45C_hz26 hx hc) (lowGeometry45C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry45C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 0 (18218431871800489 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry45C_hz24 hx hc) (lowGeometry45C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (1031122594055364631 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry45C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B 1 (26580345099286607 / 25000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry45C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (517 / 1000) (110042628711046553 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry45C_hz2 hx hc) (lowGeometry45C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (517 / 1000) (284215787713516627 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry45C_hz33 hx hc) (lowGeometry45C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (517 / 1000) (284215787713516627 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry45C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry45C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (968877405944635369 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry45C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (187744685550001151 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry45C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (19412800485870119 / 40000000000000000) (207 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry45C_hz2 hx hc) (lowGeometry45C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (233550790137476243 / 500000000000000000) (207 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry45C_hz38 hx hc) (lowGeometry45C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry45C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (193 / 400) (483 / 1000) θ) : B (233550790137476243 / 500000000000000000) (207 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry45C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry45C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (193 / 400) (483 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (87857029 / 200000000) (606248761 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (6237899 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry45C_hz12 hx hc).2
  have hrp := (lowGeometry45C_hz16 hx hc).2
  have hbn := (lowGeometry45C_hz21 hx hc).2
  have hlo := (lowGeometry45C_hz40 hx hc).1
  have hhi := (lowGeometry45C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry46W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (483 / 1000) (967 / 2000) θ := hc

theorem lowGeometry46W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry46W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (1033 / 2000) (517 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry46W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (498939 / 2000000) (499939 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry46W_hz0 hx hc) (lowGeometry46W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (499939 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry46W_hz3 hx hc) (lowGeometry46W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (1091763463473 / 195312500000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry46W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (3275290390419 / 48828125000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry46W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (483 / 500) (967 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry46W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry46W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry46W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (967 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry46W_hz7 hx hc) (lowGeometry46W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (5636130234169 / 48828125000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry46W_hz6 hx hc) (lowGeometry46W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (5636130234169 / 48828125000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry46W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry46W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (483 / 25) (967 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry46W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (967 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry46W_hz13 hx hc) (lowGeometry46W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (11508344452713 / 97656250000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry46W_hz12 hx hc) (lowGeometry46W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (11508344452713 / 97656250000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry46W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry46W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (967 / 16000000) (θ * x) := bmul (lowGeometry46W_hz0 hx hc) (lowGeometry46W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (23402710551791 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry46W_hz17 hx hc) (lowGeometry46W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (2704320071188817 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry46W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (8112960213566451 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry46W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (8112960213566451 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry46W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry46W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (483 / 125) (967 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry46W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry46W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (8649110936969187 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry46W_hz22 hx hc) (lowGeometry46W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry46W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry46W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry46W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry46W_hz26 hx hc) (lowGeometry46W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry46W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (2272964303503247 / 50000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry46W_hz24 hx hc) (lowGeometry46W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (133112960213566451 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry46W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (1134019851316385597 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry46W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (1033 / 2000) (293144131565285677 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry46W_hz2 hx hc) (lowGeometry46W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (1033 / 2000) (315873774600318147 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry46W_hz33 hx hc) (lowGeometry46W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (1033 / 2000) (315873774600318147 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry46W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry46W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (116887039786433549 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry46W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (218601281120564791 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry46W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (225815123397543429 / 500000000000000000) (517 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry46W_hz2 hx hc) (lowGeometry46W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (203085480362510959 / 500000000000000000) (517 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry46W_hz38 hx hc) (lowGeometry46W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (203085480362510959 / 500000000000000000) (517 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry46W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry46W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (483 / 1000) (967 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (2906813 / 8000000) (714184387 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (28856987 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry46W_hz12 hx hc).2
  have hrp := (lowGeometry46W_hz16 hx hc).2
  have hbn := (lowGeometry46W_hz21 hx hc).2
  have hlo := (lowGeometry46W_hz40 hx hc).1
  have hhi := (lowGeometry46W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry46C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (483 / 1000) (967 / 2000) θ := hc

theorem lowGeometry46C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry46C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (1033 / 2000) (517 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry46C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (498939 / 2000000) (499939 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry46C_hz0 hx hc) (lowGeometry46C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (499939 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry46C_hz3 hx hc) (lowGeometry46C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (1091763463473 / 195312500000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry46C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (16098707326987469 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry46C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (483 / 500) (967 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry46C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry46C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry46C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (30213914613138101 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry46C_hz7 hx hc) (lowGeometry46C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (62411329267113039 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry46C_hz6 hx hc) (lowGeometry46C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (62411329267113039 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry46C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry46C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (377223 / 50000) (755227 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry46C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (755227 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry46C_hz13 hx hc) (lowGeometry46C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (63355363017113039 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry46C_hz12 hx hc) (lowGeometry46C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (63355363017113039 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry46C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry46C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (967 / 16000000) (θ * x) := bmul (lowGeometry46C_hz0 hx hc) (lowGeometry46C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (23402710551791 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry46C_hz17 hx hc) (lowGeometry46C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (2704320071188817 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry46C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (7788441805023793 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry46C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (7788441805023793 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry46C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry46C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (157941 / 100000) (316209 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry46C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry46C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (2209577559678847 / 125000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry46C_hz22 hx hc) (lowGeometry46C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry46C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry46C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry46C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry46C_hz26 hx hc) (lowGeometry46C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry46C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 0 (18237291532123263 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry46C_hz24 hx hc) (lowGeometry46C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (257788441805023793 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry46C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B 1 (1063278091652194221 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry46C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (1033 / 2000) (549714773384184413 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry46C_hz2 hx hc) (lowGeometry46C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (1033 / 2000) (141988016229076919 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry46C_hz33 hx hc) (lowGeometry46C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (1033 / 2000) (141988016229076919 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry46C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry46C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (242211558194976207 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry46C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (234665755692953383 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry46C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (484819451261641689 / 1000000000000000000) (517 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry46C_hz2 hx hc) (lowGeometry46C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (233291079864759213 / 500000000000000000) (517 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry46C_hz38 hx hc) (lowGeometry46C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry46C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (483 / 1000) (967 / 2000) θ) : B (233291079864759213 / 500000000000000000) (517 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry46C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry46C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (483 / 1000) (967 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (438782909 / 1000000000) (605758243 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (6241133 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry46C_hz12 hx hc).2
  have hrp := (lowGeometry46C_hz16 hx hc).2
  have hbn := (lowGeometry46C_hz21 hx hc).2
  have hlo := (lowGeometry46C_hz40 hx hc).1
  have hhi := (lowGeometry46C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry47W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (967 / 2000) (121 / 250) θ := hc

theorem lowGeometry47W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry47W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (129 / 250) (1033 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry47W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (124743 / 500000) (124993 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry47W_hz0 hx hc) (lowGeometry47W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (124993 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry47W_hz3 hx hc) (lowGeometry47W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (2795006708399821 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry47W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (8385020125199463 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry47W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (967 / 1000) (121 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry47W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry47W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry47W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (121 / 2500) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry47W_hz7 hx hc) (lowGeometry47W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (14435020125199463 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry47W_hz6 hx hc) (lowGeometry47W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (14435020125199463 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry47W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry47W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (967 / 50) (484 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry47W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (121 / 50000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry47W_hz13 hx hc) (lowGeometry47W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (14737520125199463 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry47W_hz12 hx hc) (lowGeometry47W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (14737520125199463 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry47W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry47W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (121 / 2000000) (θ * x) := bmul (lowGeometry47W_hz0 hx hc) (lowGeometry47W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (7328003875969 / 62500000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry47W_hz17 hx hc) (lowGeometry47W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (2707028606418669 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry47W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (8121085819256007 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry47W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (8121085819256007 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry47W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry47W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (967 / 250) (484 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry47W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry47W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (43290276044395931 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry47W_hz22 hx hc) (lowGeometry47W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry47W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry47W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry47W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry47W_hz26 hx hc) (lowGeometry47W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry47W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (5688287088394889 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry47W_hz24 hx hc) (lowGeometry47W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (133121085819256007 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry47W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (1134158303340654257 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry47W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (129 / 250) (146448190918861981 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry47W_hz2 hx hc) (lowGeometry47W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (129 / 250) (157824765095651759 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry47W_hz33 hx hc) (lowGeometry47W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (129 / 250) (157824765095651759 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry47W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry47W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (116878914180743993 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry47W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (54642722320278877 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry47W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (56391289434527801 / 125000000000000000) (1033 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry47W_hz2 hx hc) (lowGeometry47W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (3168937646633307 / 7812500000000000) (1033 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry47W_hz38 hx hc) (lowGeometry47W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (3168937646633307 / 7812500000000000) (1033 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry47W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry47W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (967 / 2000) (121 / 250) θ) :
    OverlapGuard n θ lowWideWindow (362844583 / 1000000000) (44607469 / 62500000) ∧ radiusMinus n θ lowWideWindow ≤ (57740081 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry47W_hz12 hx hc).2
  have hrp := (lowGeometry47W_hz16 hx hc).2
  have hbn := (lowGeometry47W_hz21 hx hc).2
  have hlo := (lowGeometry47W_hz40 hx hc).1
  have hhi := (lowGeometry47W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry47C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (967 / 2000) (121 / 250) θ := hc

theorem lowGeometry47C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry47C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (129 / 250) (1033 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry47C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (124743 / 500000) (124993 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry47C_hz0 hx hc) (lowGeometry47C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (124993 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry47C_hz3 hx hc) (lowGeometry47C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (2795006708399821 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry47C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (16099238640382969 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry47C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (967 / 1000) (121 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry47C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry47C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry47C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (30245159612738037 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry47C_hz7 hx hc) (lowGeometry47C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (2497745475740159 / 40000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry47C_hz6 hx hc) (lowGeometry47C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (2497745475740159 / 40000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry47C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry47C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (755227 / 100000) (94501 / 12500) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry47C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (94501 / 100000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry47C_hz13 hx hc) (lowGeometry47C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (2535545875740159 / 40000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry47C_hz12 hx hc) (lowGeometry47C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (2535545875740159 / 40000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry47C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry47C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (121 / 2000000) (θ * x) := bmul (lowGeometry47C_hz0 hx hc) (lowGeometry47C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (7328003875969 / 62500000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry47C_hz17 hx hc) (lowGeometry47C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (2707028606418669 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry47C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (31184969545943067 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry47C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (31184969545943067 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry47C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry47C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (316209 / 200000) (39567 / 25000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry47C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry47C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (17694900333146837 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry47C_hz22 hx hc) (lowGeometry47C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry47C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry47C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry47C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry47C_hz26 hx hc) (lowGeometry47C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry47C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 0 (9128075596223019 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry47C_hz24 hx hc) (lowGeometry47C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (1031184969545943067 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry47C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B 1 (1063342441417467531 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry47C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (129 / 250) (27460818549606099 / 50000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry47C_hz2 hx hc) (lowGeometry47C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (129 / 250) (283736261092284009 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry47C_hz33 hx hc) (lowGeometry47C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (129 / 250) (283736261092284009 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry47C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry47C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (968815030454056933 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry47C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (469301281616847631 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry47C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (96863784525717351 / 200000000000000000) (1033 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry47C_hz2 hx hc) (lowGeometry47C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (466062771436140717 / 1000000000000000000) (1033 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry47C_hz38 hx hc) (lowGeometry47C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry47C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (967 / 2000) (121 / 250) θ) : B (466062771436140717 / 1000000000000000000) (1033 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry47C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry47C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (967 / 2000) (121 / 250) θ) :
    OverlapGuard n θ lowCoreWindow (438280747 / 1000000000) (121053527 / 200000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62443637 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry47C_hz12 hx hc).2
  have hrp := (lowGeometry47C_hz16 hx hc).2
  have hbn := (lowGeometry47C_hz21 hx hc).2
  have hlo := (lowGeometry47C_hz40 hx hc).1
  have hhi := (lowGeometry47C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry48W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (121 / 250) (969 / 2000) θ := hc

theorem lowGeometry48W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry48W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (1031 / 2000) (129 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry48W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (124751 / 500000) (125001 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry48W_hz0 hx hc) (lowGeometry48W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (125001 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry48W_hz3 hx hc) (lowGeometry48W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (5590192304384529 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry48W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (16770576913153587 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry48W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (121 / 125) (969 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry48W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry48W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry48W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (969 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry48W_hz7 hx hc) (lowGeometry48W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (28883076913153587 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry48W_hz6 hx hc) (lowGeometry48W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (28883076913153587 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry48W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry48W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (484 / 25) (969 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry48W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (969 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry48W_hz13 hx hc) (lowGeometry48W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (29488701913153587 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry48W_hz12 hx hc) (lowGeometry48W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (29488701913153587 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry48W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry48W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (969 / 16000000) (θ * x) := bmul (lowGeometry48W_hz0 hx hc) (lowGeometry48W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (117483026188167 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry48W_hz17 hx hc) (lowGeometry48W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (1083895872250499 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry48W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (3251687616751497 / 50000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry48W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (3251687616751497 / 50000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry48W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry48W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (484 / 125) (969 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry48W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry48W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (43334997403945927 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry48W_hz22 hx hc) (lowGeometry48W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry48W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry48W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry48W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry48W_hz26 hx hc) (lowGeometry48W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry48W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (9110661468850657 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry48W_hz24 hx hc) (lowGeometry48W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (53251687616751497 / 50000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry48W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (1134296893612833893 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry48W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (1031 / 2000) (585297197104222289 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry48W_hz2 hx hc) (lowGeometry48W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (1031 / 2000) (315425252224237787 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry48W_hz33 hx hc) (lowGeometry48W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (1031 / 2000) (315425252224237787 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry48W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry48W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (46748312383248503 / 50000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry48W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (218540471068178533 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry48W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (90126090268516827 / 200000000000000000) (129 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry48W_hz2 hx hc) (lowGeometry48W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (8101542879966617 / 20000000000000000) (129 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry48W_hz38 hx hc) (lowGeometry48W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (8101542879966617 / 20000000000000000) (129 / 250) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry48W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry48W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (121 / 250) (969 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (362337673 / 1000000000) (178313609 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (28883077 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry48W_hz12 hx hc).2
  have hrp := (lowGeometry48W_hz16 hx hc).2
  have hbn := (lowGeometry48W_hz21 hx hc).2
  have hlo := (lowGeometry48W_hz40 hx hc).1
  have hhi := (lowGeometry48W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry48C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (121 / 250) (969 / 2000) θ := hc

theorem lowGeometry48C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry48C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (1031 / 2000) (129 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry48C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (124751 / 500000) (125001 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry48C_hz0 hx hc) (lowGeometry48C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (125001 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry48C_hz3 hx hc) (lowGeometry48C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (5590192304384529 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry48C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (4024938459156861 / 125000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry48C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (121 / 125) (969 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry48C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry48C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry48C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (30276404612337973 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry48C_hz7 hx hc) (lowGeometry48C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (62475912285592861 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry48C_hz6 hx hc) (lowGeometry48C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (62475912285592861 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry48C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry48C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (94501 / 12500) (756789 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry48C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (756789 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry48C_hz13 hx hc) (lowGeometry48C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (63421898535592861 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry48C_hz12 hx hc) (lowGeometry48C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (63421898535592861 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry48C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry48C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (969 / 16000000) (θ * x) := bmul (lowGeometry48C_hz0 hx hc) (lowGeometry48C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (117483026188167 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry48C_hz17 hx hc) (lowGeometry48C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (1083895872250499 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry48C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (7804050280203593 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry48C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (7804050280203593 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry48C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry48C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (39567 / 25000) (316863 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry48C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry48C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (8856590094431449 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry48C_hz22 hx hc) (lowGeometry48C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry48C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry48C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry48C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry48C_hz26 hx hc) (lowGeometry48C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry48C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 0 (18275010852768813 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry48C_hz24 hx hc) (lowGeometry48C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (257804050280203593 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry48C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B 1 (1063406853454043877 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry48C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (1031 / 2000) (548717936382286641 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry48C_hz2 hx hc) (lowGeometry48C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (1031 / 2000) (283496473617527727 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry48C_hz33 hx hc) (lowGeometry48C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (1031 / 2000) (283496473617527727 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry48C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry48C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (242195949719796407 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry48C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (234635512242696597 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry48C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (483818426244440383 / 1000000000000000000) (129 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry48C_hz2 hx hc) (lowGeometry48C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (46554341539167157 / 100000000000000000) (129 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry48C_hz38 hx hc) (lowGeometry48C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry48C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (121 / 250) (969 / 2000) θ) : B (46554341539167157 / 100000000000000000) (129 / 250) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry48C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry48C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (121 / 250) (969 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (437778661 / 1000000000) (604776939 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62475913 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry48C_hz12 hx hc).2
  have hrp := (lowGeometry48C_hz16 hx hc).2
  have hbn := (lowGeometry48C_hz21 hx hc).2
  have hlo := (lowGeometry48C_hz40 hx hc).1
  have hhi := (lowGeometry48C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry49W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (969 / 2000) (97 / 200) θ := hc

theorem lowGeometry49W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry49W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (103 / 200) (1031 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry49W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (99807 / 400000) (100007 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry49W_hz0 hx hc) (lowGeometry49W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (100007 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry49W_hz3 hx hc) (lowGeometry49W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (5590365596273647 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry49W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (16771096788820941 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry49W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (969 / 1000) (97 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry49W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry49W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry49W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (97 / 2000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry49W_hz7 hx hc) (lowGeometry49W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (28896096788820941 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry49W_hz6 hx hc) (lowGeometry49W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (28896096788820941 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry49W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry49W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (969 / 50) (97 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry49W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (97 / 40000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry49W_hz13 hx hc) (lowGeometry49W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (29502346788820941 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry49W_hz12 hx hc) (lowGeometry49W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (29502346788820941 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry49W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry49W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (97 / 1600000) (θ * x) := bmul (lowGeometry49W_hz0 hx hc) (lowGeometry49W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (58859223300971 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry49W_hz17 hx hc) (lowGeometry49W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (10849813205854837 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry49W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (32549439617564511 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry49W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (32549439617564511 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry49W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry49W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (969 / 250) (97 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry49W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry49W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (43379718763495923 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry49W_hz22 hx hc) (lowGeometry49W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry49W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry49W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry49W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry49W_hz26 hx hc) (lowGeometry49W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry49W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (22800158990673729 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry49W_hz24 hx hc) (lowGeometry49W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (532549439617564511 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry49W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (1134435622547927957 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry49W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (103 / 200) (292400781711728431 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry49W_hz2 hx hc) (lowGeometry49W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (103 / 200) (3940011758780027 / 6250000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry49W_hz33 hx hc) (lowGeometry49W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (103 / 200) (3940011758780027 / 6250000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry49W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry49W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (467450560382435489 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry49W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (218510026401852967 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry49W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (56266331798477139 / 125000000000000000) (1031 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry49W_hz2 hx hc) (lowGeometry49W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (202265168203234827 / 500000000000000000) (1031 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry49W_hz38 hx hc) (lowGeometry49W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (202265168203234827 / 500000000000000000) (1031 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry49W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry49W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (969 / 2000) (97 / 200) θ) :
    OverlapGuard n θ lowWideWindow (180915447 / 500000000) (712789183 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (28896097 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry49W_hz12 hx hc).2
  have hrp := (lowGeometry49W_hz16 hx hc).2
  have hbn := (lowGeometry49W_hz21 hx hc).2
  have hlo := (lowGeometry49W_hz40 hx hc).1
  have hhi := (lowGeometry49W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry49C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (969 / 2000) (97 / 200) θ := hc

theorem lowGeometry49C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry49C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (103 / 200) (1031 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry49C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (99807 / 400000) (100007 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry49C_hz0 hx hc) (lowGeometry49C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (100007 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry49C_hz3 hx hc) (lowGeometry49C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (5590365596273647 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry49C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (32200505834536207 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry49C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (969 / 1000) (97 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry49C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry49C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry49C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (30307649611937909 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry49C_hz7 hx hc) (lowGeometry49C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (15627038861618529 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry49C_hz6 hx hc) (lowGeometry49C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (15627038861618529 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry49C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry49C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (756789 / 100000) (75757 / 10000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry49C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (75757 / 80000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry49C_hz13 hx hc) (lowGeometry49C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (15863779486618529 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry49C_hz12 hx hc) (lowGeometry49C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (15863779486618529 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry49C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry49C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (97 / 1600000) (θ * x) := bmul (lowGeometry49C_hz0 hx hc) (lowGeometry49C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (58859223300971 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry49C_hz17 hx hc) (lowGeometry49C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (10849813205854837 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry49C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (31247462032861931 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry49C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (31247462032861931 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry49C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry49C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (316863 / 200000) (31719 / 20000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry49C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry49C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (17731460044578959 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry49C_hz22 hx hc) (lowGeometry49C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry49C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry49C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry49C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry49C_hz26 hx hc) (lowGeometry49C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry49C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 0 (4573467628272897 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry49C_hz24 hx hc) (lowGeometry49C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (1031247462032861931 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry49C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B 1 (106347132794921901 / 100000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry49C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (103 / 200) (342637168473639 / 625000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry49C_hz2 hx hc) (lowGeometry49C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (103 / 200) (141628335017728497 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry49C_hz33 hx hc) (lowGeometry49C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (103 / 200) (141628335017728497 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry49C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry49C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (968752537967138069 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry49C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (187696295963554257 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry49C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (483317962106152211 / 1000000000000000000) (1031 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry49C_hz2 hx hc) (lowGeometry49C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (465024091593060623 / 1000000000000000000) (1031 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry49C_hz38 hx hc) (lowGeometry49C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry49C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (969 / 2000) (97 / 200) θ) : B (465024091593060623 / 1000000000000000000) (1031 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry49C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry49C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (969 / 2000) (97 / 200) θ) :
    OverlapGuard n θ lowCoreWindow (8745533 / 20000000) (604286153 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15627039 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry49C_hz12 hx hc).2
  have hrp := (lowGeometry49C_hz16 hx hc).2
  have hbn := (lowGeometry49C_hz21 hx hc).2
  have hlo := (lowGeometry49C_hz40 hx hc).1
  have hhi := (lowGeometry49C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry50W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (97 / 200) (971 / 2000) θ := hc

theorem lowGeometry50W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry50W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (1029 / 2000) (103 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry50W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (99813 / 400000) (100013 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry50W_hz0 hx hc) (lowGeometry50W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (100013 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry50W_hz3 hx hc) (lowGeometry50W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (698816661623419 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry50W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (2096449984870257 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry50W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (97 / 100) (971 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry50W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry50W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry50W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (971 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry50W_hz7 hx hc) (lowGeometry50W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (3613637484870257 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry50W_hz6 hx hc) (lowGeometry50W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (3613637484870257 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry50W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry50W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (97 / 5) (971 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry50W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (971 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry50W_hz13 hx hc) (lowGeometry50W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (3689496859870257 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry50W_hz12 hx hc) (lowGeometry50W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (3689496859870257 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry50W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry50W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (971 / 16000000) (θ * x) := bmul (lowGeometry50W_hz0 hx hc) (lowGeometry50W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (58977162293489 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry50W_hz17 hx hc) (lowGeometry50W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (1086067790641901 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry50W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (3258203371925703 / 50000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry50W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (3258203371925703 / 50000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry50W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry50W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (97 / 25) (971 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry50W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry50W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (21712220061522959 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry50W_hz22 hx hc) (lowGeometry50W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry50W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry50W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry50W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry50W_hz26 hx hc) (lowGeometry50W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry50W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (4564732861844163 / 100000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry50W_hz24 hx hc) (lowGeometry50W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (53258203371925703 / 50000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry50W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (1134574490562159329 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry50W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (1029 / 2000) (116861172527902411 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry50W_hz2 hx hc) (lowGeometry50W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (1029 / 2000) (125990638251590737 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry50W_hz33 hx hc) (lowGeometry50W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (1029 / 2000) (125990638251590737 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry50W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry50W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (46741796628074297 / 50000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry50W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (54619888800506443 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry50W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (224815462302884519 / 500000000000000000) (103 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry50W_hz2 hx hc) (lowGeometry50W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (25248974749207963 / 62500000000000000) (103 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry50W_hz38 hx hc) (lowGeometry50W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (25248974749207963 / 62500000000000000) (103 / 200) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry50W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry50W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (97 / 200) (971 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (180662123 / 500000000) (142464749 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (289091 / 2500000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry50W_hz12 hx hc).2
  have hrp := (lowGeometry50W_hz16 hx hc).2
  have hbn := (lowGeometry50W_hz21 hx hc).2
  have hlo := (lowGeometry50W_hz40 hx hc).1
  have hhi := (lowGeometry50W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry50C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (97 / 200) (971 / 2000) θ := hc

theorem lowGeometry50C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry50C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (1029 / 2000) (103 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry50C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (99813 / 400000) (100013 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry50C_hz0 hx hc) (lowGeometry50C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (100013 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry50C_hz3 hx hc) (lowGeometry50C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (698816661623419 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry50C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (8050367941901787 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry50C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (97 / 100) (971 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry50C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry50C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry50C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (6067778922307569 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry50C_hz7 hx hc) (lowGeometry50C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (62540366379144993 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry50C_hz6 hx hc) (lowGeometry50C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (62540366379144993 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry50C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry50C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (75757 / 10000) (758351 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry50C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (758351 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry50C_hz13 hx hc) (lowGeometry50C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (63488305129144993 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry50C_hz12 hx hc) (lowGeometry50C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (63488305129144993 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry50C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry50C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (971 / 16000000) (θ * x) := bmul (lowGeometry50C_hz0 hx hc) (lowGeometry50C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (58977162293489 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry50C_hz17 hx hc) (lowGeometry50C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (1086067790641901 / 100000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry50C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (31278752370486749 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry50C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (31278752370486749 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry50C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry50C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (31719 / 20000) (317517 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry50C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry50C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (17749739900295019 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry50C_hz22 hx hc) (lowGeometry50C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry50C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry50C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry50C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry50C_hz26 hx hc) (lowGeometry50C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry50C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 0 (9156365086707181 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry50C_hz24 hx hc) (lowGeometry50C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (1031278752370486749 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry50C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B 1 (1063535865090827729 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry50C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (1029 / 2000) (547720970521776281 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry50C_hz2 hx hc) (lowGeometry50C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (1029 / 2000) (566033700695190643 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry50C_hz33 hx hc) (lowGeometry50C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (1029 / 2000) (566033700695190643 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry50C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry50C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (968721247629513251 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry50C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (234605213902220183 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry50C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (30176095638173071 / 62500000000000000) (103 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry50C_hz2 hx hc) (lowGeometry50C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (232252400018677387 / 500000000000000000) (103 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry50C_hz38 hx hc) (lowGeometry50C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry50C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (97 / 200) (971 / 2000) θ) : B (232252400018677387 / 500000000000000000) (103 / 200) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry50C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry50C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (97 / 200) (971 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (436774713 / 1000000000) (603795279 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62540367 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry50C_hz12 hx hc).2
  have hrp := (lowGeometry50C_hz16 hx hc).2
  have hbn := (lowGeometry50C_hz21 hx hc).2
  have hlo := (lowGeometry50C_hz40 hx hc).1
  have hhi := (lowGeometry50C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry51W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (971 / 2000) (243 / 500) θ := hc

theorem lowGeometry51W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry51W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (257 / 500) (1029 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry51W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (249547 / 1000000) (250047 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry51W_hz0 hx hc) (lowGeometry51W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (250047 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry51W_hz3 hx hc) (lowGeometry51W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (2795347697514569 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry51W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (8386043092543707 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry51W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (971 / 1000) (243 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry51W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry51W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry51W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (243 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry51W_hz7 hx hc) (lowGeometry51W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (14461043092543707 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry51W_hz6 hx hc) (lowGeometry51W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (14461043092543707 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry51W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry51W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (971 / 50) (486 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry51W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (243 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry51W_hz13 hx hc) (lowGeometry51W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (14764793092543707 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry51W_hz12 hx hc) (lowGeometry51W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (14764793092543707 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry51W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry51W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (243 / 4000000) (θ * x) := bmul (lowGeometry51W_hz0 hx hc) (lowGeometry51W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (590953307393 / 5000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry51W_hz17 hx hc) (lowGeometry51W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (5435776427489453 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry51W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (16307329282468359 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry51W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (16307329282468359 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry51W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry51W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (971 / 250) (486 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry51W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry51W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (21734580741297957 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry51W_hz22 hx hc) (lowGeometry51W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry51W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry51W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry51W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry51W_hz26 hx hc) (lowGeometry51W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry51W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (45694339255535803 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry51W_hz24 hx hc) (lowGeometry51W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (266307329282468359 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry51W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (1134713498072976473 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry51W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (257 / 500) (145952523689636599 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry51W_hz2 hx hc) (lowGeometry51W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (257 / 500) (629504434014082199 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry51W_hz33 hx hc) (lowGeometry51W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (257 / 500) (629504434014082199 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry51W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry51W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (233692670717531641 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry51W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (109224528694185341 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry51W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (224565630995245061 / 500000000000000000) (1029 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry51W_hz2 hx hc) (lowGeometry51W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (403436922734954319 / 1000000000000000000) (1029 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry51W_hz38 hx hc) (lowGeometry51W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (403436922734954319 / 1000000000000000000) (1029 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry51W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry51W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (971 / 2000) (243 / 500) θ) :
    OverlapGuard n θ lowWideWindow (360817729 / 1000000000) (355929061 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (23137669 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry51W_hz12 hx hc).2
  have hrp := (lowGeometry51W_hz16 hx hc).2
  have hbn := (lowGeometry51W_hz21 hx hc).2
  have hlo := (lowGeometry51W_hz40 hx hc).1
  have hhi := (lowGeometry51W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry51C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (971 / 2000) (243 / 500) θ := hc

theorem lowGeometry51C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry51C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (257 / 500) (1029 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry51C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (249547 / 1000000) (250047 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry51C_hz0 hx hc) (lowGeometry51C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (250047 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry51C_hz3 hx hc) (lowGeometry51C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (2795347697514569 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry51C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (6440481095073567 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry51C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (971 / 1000) (243 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry51C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry51C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry51C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (30370139611137781 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry51C_hz7 hx hc) (lowGeometry51C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (3910784067906601 / 62500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry51C_hz6 hx hc) (lowGeometry51C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (3910784067906601 / 62500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry51C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry51C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (758351 / 100000) (189783 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry51C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (189783 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry51C_hz13 hx hc) (lowGeometry51C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (3970091255406601 / 62500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry51C_hz12 hx hc) (lowGeometry51C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (3970091255406601 / 62500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry51C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry51C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (243 / 4000000) (θ * x) := bmul (lowGeometry51C_hz0 hx hc) (lowGeometry51C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (590953307393 / 5000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry51C_hz17 hx hc) (lowGeometry51C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (5435776427489453 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry51C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (125240288889357 / 4000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry51C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (125240288889357 / 4000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry51C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry51C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (317517 / 200000) (79461 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry51C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry51C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (444200493900277 / 25000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry51C_hz22 hx hc) (lowGeometry51C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry51C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry51C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry51C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry51C_hz26 hx hc) (lowGeometry51C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry51C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 0 (18331589833737137 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry51C_hz24 hx hc) (lowGeometry51C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (4125240288889357 / 4000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry51C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B 1 (5318002325336233 / 5000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry51C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (257 / 500) (68402804909637297 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry51C_hz2 hx hc) (lowGeometry51C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (257 / 500) (565554029110835513 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry51C_hz33 hx hc) (lowGeometry51C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (257 / 500) (565554029110835513 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry51C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry51C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (3874759711110643 / 4000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry51C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (938360176177889599 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry51C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (482317130555435253 / 1000000000000000000) (1029 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry51C_hz2 hx hc) (lowGeometry51C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (115996385180424529 / 250000000000000000) (1029 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry51C_hz38 hx hc) (lowGeometry51C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry51C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (971 / 2000) (243 / 500) θ) : B (115996385180424529 / 250000000000000000) (1029 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry51C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry51C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (971 / 2000) (243 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (109068213 / 250000000) (150826079 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31286273 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry51C_hz12 hx hc).2
  have hrp := (lowGeometry51C_hz16 hx hc).2
  have hbn := (lowGeometry51C_hz21 hx hc).2
  have hlo := (lowGeometry51C_hz40 hx hc).1
  have hhi := (lowGeometry51C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry52W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (243 / 500) (973 / 2000) θ := hc

theorem lowGeometry52W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry52W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (1027 / 2000) (257 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry52W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (249561 / 1000000) (250061 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry52W_hz0 hx hc) (lowGeometry52W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (250061 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry52W_hz3 hx hc) (lowGeometry52W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (2795425951442821 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry52W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (8386277854328463 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry52W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (243 / 250) (973 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry52W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry52W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry52W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (973 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry52W_hz7 hx hc) (lowGeometry52W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (14467527854328463 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry52W_hz6 hx hc) (lowGeometry52W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (14467527854328463 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry52W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry52W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (486 / 25) (973 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry52W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (973 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry52W_hz13 hx hc) (lowGeometry52W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (14771590354328463 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry52W_hz12 hx hc) (lowGeometry52W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (14771590354328463 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry52W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry52W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (973 / 16000000) (θ * x) := bmul (lowGeometry52W_hz0 hx hc) (lowGeometry52W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (118427458617333 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry52W_hz17 hx hc) (lowGeometry52W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (2176487616480581 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry52W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (6529462849441743 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry52W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (6529462849441743 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry52W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry52W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (486 / 125) (973 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry52W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry52W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (4351388284214591 / 100000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry52W_hz22 hx hc) (lowGeometry52W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry52W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry52W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry52W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry52W_hz26 hx hc) (lowGeometry52W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry52W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (5717668736578747 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry52W_hz24 hx hc) (lowGeometry52W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (106529462849441743 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry52W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (1134852645499058849 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry52W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (1027 / 2000) (583314259786516249 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry52W_hz2 hx hc) (lowGeometry52W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (1027 / 2000) (25162224387165849 / 40000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry52W_hz33 hx hc) (lowGeometry52W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (1027 / 2000) (25162224387165849 / 40000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry52W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry52W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (93470537150558257 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry52W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (109209266440173641 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry52W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (448631666536233317 / 1000000000000000000) (257 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry52W_hz2 hx hc) (lowGeometry52W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (402890316643603341 / 1000000000000000000) (257 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry52W_hz38 hx hc) (lowGeometry52W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (402890316643603341 / 1000000000000000000) (257 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry52W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry52W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (243 / 500) (973 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (22519459 / 62500000) (142278463 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (115740223 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry52W_hz12 hx hc).2
  have hrp := (lowGeometry52W_hz16 hx hc).2
  have hbn := (lowGeometry52W_hz21 hx hc).2
  have hlo := (lowGeometry52W_hz40 hx hc).1
  have hhi := (lowGeometry52W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry52C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (243 / 500) (973 / 2000) θ := hc

theorem lowGeometry52C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry52C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (1027 / 2000) (257 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry52C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (249561 / 1000000) (250061 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry52C_hz0 hx hc) (lowGeometry52C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (250061 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry52C_hz3 hx hc) (lowGeometry52C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (2795425951442821 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry52C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (16101653480310649 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry52C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (243 / 250) (973 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry52C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry52C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry52C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (30401384610737717 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry52C_hz7 hx hc) (lowGeometry52C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (12520938314271803 / 200000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry52C_hz6 hx hc) (lowGeometry52C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (12520938314271803 / 200000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry52C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry52C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (189783 / 25000) (759913 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry52C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (759913 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry52C_hz13 hx hc) (lowGeometry52C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (12710916564271803 / 200000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry52C_hz12 hx hc) (lowGeometry52C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (12710916564271803 / 200000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry52C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry52C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (973 / 16000000) (θ * x) := bmul (lowGeometry52C_hz0 hx hc) (lowGeometry52C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (118427458617333 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry52C_hz17 hx hc) (lowGeometry52C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (2176487616480581 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry52C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (31341421677320367 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry52C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (31341421677320367 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry52C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry52C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (79461 / 50000) (318171 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry52C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry52C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (17786299611727141 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry52C_hz22 hx hc) (lowGeometry52C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry52C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry52C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry52C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry52C_hz26 hx hc) (lowGeometry52C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry52C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 0 (2293806186757489 / 125000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry52C_hz24 hx hc) (lowGeometry52C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (1031341421677320367 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry52C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B 1 (531832564033698171 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry52C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (1027 / 2000) (13668096895666043 / 25000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry52C_hz2 hx hc) (lowGeometry52C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (1027 / 2000) (8829286333135963 / 15625000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry52C_hz33 hx hc) (lowGeometry52C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (1027 / 2000) (8829286333135963 / 15625000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry52C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry52C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (968658578322679633 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry52C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (938299441358114873 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry52C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (481816763137391987 / 1000000000000000000) (257 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry52C_hz2 hx hc) (lowGeometry52C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (18538652545733283 / 40000000000000000) (257 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry52C_hz38 hx hc) (lowGeometry52C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry52C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (243 / 500) (973 / 2000) θ) : B (18538652545733283 / 40000000000000000) (257 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry52C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry52C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (243 / 500) (973 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (87154213 / 200000000) (37675829 / 62500000) ∧ radiusMinus n θ lowCoreWindow ≤ (15651173 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry52C_hz12 hx hc).2
  have hrp := (lowGeometry52C_hz16 hx hc).2
  have hbn := (lowGeometry52C_hz21 hx hc).2
  have hlo := (lowGeometry52C_hz40 hx hc).1
  have hhi := (lowGeometry52C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry53W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (973 / 2000) (487 / 1000) θ := hc

theorem lowGeometry53W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry53W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (513 / 1000) (1027 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry53W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (499149 / 2000000) (500149 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry53W_hz0 hx hc) (lowGeometry53W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (500149 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry53W_hz3 hx hc) (lowGeometry53W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (174718838032083 / 31250000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry53W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (524156514096249 / 7812500000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry53W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (973 / 1000) (487 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry53W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry53W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry53W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (487 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry53W_hz7 hx hc) (lowGeometry53W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (904625264096249 / 7812500000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry53W_hz6 hx hc) (lowGeometry53W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (904625264096249 / 7812500000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry53W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry53W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (973 / 50) (487 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry53W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (487 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry53W_hz13 hx hc) (lowGeometry53W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (923648701596249 / 7812500000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry53W_hz12 hx hc) (lowGeometry53W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (923648701596249 / 7812500000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry53W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry53W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (487 / 8000000) (θ * x) := bmul (lowGeometry53W_hz0 hx hc) (lowGeometry53W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (1854136208577 / 15625000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry53W_hz17 hx hc) (lowGeometry53W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (2178666723929367 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry53W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (6536000171788101 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry53W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (6536000171788101 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry53W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry53W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (973 / 250) (487 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry53W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry53W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (21779302100847953 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry53W_hz22 hx hc) (lowGeometry53W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry53W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry53W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry53W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry53W_hz26 hx hc) (lowGeometry53W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry53W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (45788360529724149 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry53W_hz24 hx hc) (lowGeometry53W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (106536000171788101 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry53W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (1134991933260323429 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry53W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (513 / 1000) (582818357729176081 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry53W_hz2 hx hc) (lowGeometry53W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (513 / 1000) (62860671825890023 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry53W_hz33 hx hc) (lowGeometry53W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (513 / 1000) (62860671825890023 / 100000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry53W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry53W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (93463999828211899 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry53W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (218387981597199847 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry53W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (224066069118727043 / 500000000000000000) (1027 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry53W_hz2 hx hc) (lowGeometry53W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (402343777707729937 / 1000000000000000000) (1027 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry53W_hz38 hx hc) (lowGeometry53W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (402343777707729937 / 1000000000000000000) (1027 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry53W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry53W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (973 / 2000) (487 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (359805089 / 1000000000) (177731581 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (57896017 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry53W_hz12 hx hc).2
  have hrp := (lowGeometry53W_hz16 hx hc).2
  have hbn := (lowGeometry53W_hz21 hx hc).2
  have hlo := (lowGeometry53W_hz40 hx hc).1
  have hhi := (lowGeometry53W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry53C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (973 / 2000) (487 / 1000) θ := hc

theorem lowGeometry53C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry53C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (513 / 1000) (1027 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry53C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (499149 / 2000000) (500149 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry53C_hz0 hx hc) (lowGeometry53C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (500149 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry53C_hz3 hx hc) (lowGeometry53C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (174718838032083 / 31250000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry53C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (32204176226073539 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry53C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (973 / 1000) (487 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry53C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry53C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry53C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (30432629610337653 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry53C_hz7 hx hc) (lowGeometry53C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (7829600729551399 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry53C_hz6 hx hc) (lowGeometry53C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (7829600729551399 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry53C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry53C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (759913 / 100000) (380347 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry53C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (380347 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry53C_hz13 hx hc) (lowGeometry53C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (7948459167051399 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry53C_hz12 hx hc) (lowGeometry53C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (7948459167051399 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry53C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry53C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (487 / 8000000) (θ * x) := bmul (lowGeometry53C_hz0 hx hc) (lowGeometry53C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (1854136208577 / 15625000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry53C_hz17 hx hc) (lowGeometry53C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (2178666723929367 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry53C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (6274560164916577 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry53C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (6274560164916577 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry53C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry53C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (318171 / 200000) (159249 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry53C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry53C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (8902289733721601 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry53C_hz22 hx hc) (lowGeometry53C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry53C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry53C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry53C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry53C_hz26 hx hc) (lowGeometry53C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry53C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 0 (18369309154382687 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry53C_hz24 hx hc) (lowGeometry53C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (206274560164916577 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry53C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B 1 (1063729854280744719 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry53C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (513 / 1000) (273112640086581207 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry53C_hz2 hx hc) (lowGeometry53C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (513 / 1000) (564594589327545101 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry53C_hz33 hx hc) (lowGeometry53C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (513 / 1000) (564594589327545101 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry53C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry53C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (193725439835083423 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry53C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (469119325491206589 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry53C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (12032910698849449 / 25000000000000000) (1027 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry53C_hz2 hx hc) (lowGeometry53C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (462947118799595273 / 1000000000000000000) (1027 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry53C_hz38 hx hc) (lowGeometry53C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry53C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (973 / 2000) (487 / 1000) θ) : B (462947118799595273 / 1000000000000000000) (1027 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry53C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry53C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (973 / 2000) (487 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (435269353 / 1000000000) (150580531 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31318403 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry53C_hz12 hx hc).2
  have hrp := (lowGeometry53C_hz16 hx hc).2
  have hbn := (lowGeometry53C_hz21 hx hc).2
  have hlo := (lowGeometry53C_hz40 hx hc).1
  have hhi := (lowGeometry53C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry54W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (487 / 1000) (39 / 80) θ := hc

theorem lowGeometry54W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry54W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (41 / 80) (513 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry54W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (19967 / 80000) (20007 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry54W_hz0 hx hc) (lowGeometry54W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (20007 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry54W_hz3 hx hc) (lowGeometry54W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (559114813790513 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry54W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (1677344441371539 / 25000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry54W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (487 / 500) (39 / 40) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry54W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry54W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry54W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (39 / 800) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry54W_hz7 hx hc) (lowGeometry54W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (2896094441371539 / 25000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry54W_hz6 hx hc) (lowGeometry54W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (2896094441371539 / 25000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry54W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry54W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (487 / 25) (39 / 2) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry54W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (39 / 16000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry54W_hz13 hx hc) (lowGeometry54W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (2957031941371539 / 25000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry54W_hz12 hx hc) (lowGeometry54W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (2957031941371539 / 25000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry54W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry54W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (39 / 640000) (θ * x) := bmul (lowGeometry54W_hz0 hx hc) (lowGeometry54W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (118902439024391 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry54W_hz17 hx hc) (lowGeometry54W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (5452119748877289 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry54W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (16356359246631867 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry54W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (16356359246631867 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry54W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry54W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (487 / 125) (39 / 10) (θ * (8 : ℝ)) := bmul (lowGeometry54W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry54W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (21801662780622951 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry54W_hz22 hx hc) (lowGeometry54W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry54W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry54W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry54W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry54W_hz26 hx hc) (lowGeometry54W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry54W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (45835371166818321 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry54W_hz24 hx hc) (lowGeometry54W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (266356359246631867 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry54W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (1135131361777933013 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry54W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (41 / 80) (145580597148019909 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry54W_hz2 hx hc) (lowGeometry54W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (41 / 80) (628157759758897957 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry54W_hz33 hx hc) (lowGeometry54W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (41 / 80) (628157759758897957 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry54W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry54W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (233643640753368133 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry54W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (43671480691591157 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry54W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (447632677088809359 / 1000000000000000000) (513 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry54W_hz2 hx hc) (lowGeometry54W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (200898652960995519 / 500000000000000000) (513 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry54W_hz38 hx hc) (lowGeometry54W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (200898652960995519 / 500000000000000000) (513 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry54W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry54W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (487 / 1000) (39 / 80) θ) :
    OverlapGuard n θ lowWideWindow (71859793 / 200000000) (177615037 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (57921889 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry54W_hz12 hx hc).2
  have hrp := (lowGeometry54W_hz16 hx hc).2
  have hbn := (lowGeometry54W_hz21 hx hc).2
  have hlo := (lowGeometry54W_hz40 hx hc).1
  have hhi := (lowGeometry54W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry54C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (487 / 1000) (39 / 80) θ := hc

theorem lowGeometry54C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry54C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (41 / 80) (513 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry54C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (19967 / 80000) (20007 / 80000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry54C_hz0 hx hc) (lowGeometry54C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (20007 / 640000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry54C_hz3 hx hc) (lowGeometry54C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (559114813790513 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry54C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (32205013274333549 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry54C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (487 / 500) (39 / 40) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry54C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry54C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry54C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (30463874609937589 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry54C_hz7 hx hc) (lowGeometry54C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (31334443942135569 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry54C_hz6 hx hc) (lowGeometry54C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (31334443942135569 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry54C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry54C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (380347 / 50000) (30459 / 4000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry54C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (30459 / 32000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry54C_hz13 hx hc) (lowGeometry54C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (31810365817135569 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry54C_hz12 hx hc) (lowGeometry54C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (31810365817135569 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry54C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry54C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (39 / 640000) (θ * x) := bmul (lowGeometry54C_hz0 hx hc) (lowGeometry54C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (118902439024391 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry54C_hz17 hx hc) (lowGeometry54C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (5452119748877289 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry54C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (6280841950706637 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry54C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (6280841950706637 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry54C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry54C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (159249 / 100000) (12753 / 8000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry54C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry54C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (17822859323159263 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry54C_hz22 hx hc) (lowGeometry54C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry54C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry54C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry54C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry54C_hz26 hx hc) (lowGeometry54C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry54C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 0 (9194084407352731 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry54C_hz24 hx hc) (lowGeometry54C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (206280841950706637 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry54C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B 1 (1063794643897310279 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry54C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (41 / 80) (272863326159660087 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry54C_hz2 hx hc) (lowGeometry54C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (41 / 80) (141028705283506409 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry54C_hz33 hx hc) (lowGeometry54C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (41 / 80) (141028705283506409 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry54C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry54C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (193719158049293363 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry54C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (469088902441588769 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry54C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (60102015625328561 / 125000000000000000) (513 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry54C_hz2 hx hc) (lowGeometry54C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (231213978093961513 / 500000000000000000) (513 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry54C_hz38 hx hc) (lowGeometry54C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry54C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (487 / 1000) (39 / 80) θ) : B (231213978093961513 / 500000000000000000) (513 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry54C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry54C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (487 / 1000) (39 / 80) θ) :
    OverlapGuard n θ lowCoreWindow (108691929 / 250000000) (300915447 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (7833611 / 125000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry54C_hz12 hx hc).2
  have hrp := (lowGeometry54C_hz16 hx hc).2
  have hbn := (lowGeometry54C_hz21 hx hc).2
  have hlo := (lowGeometry54C_hz40 hx hc).1
  have hhi := (lowGeometry54C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry55W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (39 / 80) (61 / 125) θ := hc

theorem lowGeometry55W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry55W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (64 / 125) (41 / 80) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry55W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (156 / 625) (2501 / 10000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry55W_hz0 hx hc) (lowGeometry55W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (2501 / 80000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry55W_hz3 hx hc) (lowGeometry55W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (5591287865957181 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry55W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (16773863597871543 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry55W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (39 / 40) (122 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry55W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry55W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry55W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (61 / 1250) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry55W_hz7 hx hc) (lowGeometry55W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (28973863597871543 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry55W_hz6 hx hc) (lowGeometry55W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (28973863597871543 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry55W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry55W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (39 / 2) (488 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry55W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (61 / 25000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry55W_hz13 hx hc) (lowGeometry55W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (29583863597871543 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry55W_hz12 hx hc) (lowGeometry55W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (29583863597871543 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry55W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry55W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (61 / 1000000) (θ * x) := bmul (lowGeometry55W_hz0 hx hc) (lowGeometry55W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (61 / 512000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry55W_hz17 hx hc) (lowGeometry55W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (10915155747858113 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry55W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (32745467243574339 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry55W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (32745467243574339 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry55W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry55W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (39 / 10) (488 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry55W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry55W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (43648046920795897 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry55W_hz22 hx hc) (lowGeometry55W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry55W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry55W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry55W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry55W_hz26 hx hc) (lowGeometry55W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry55W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (45882381803912493 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry55W_hz24 hx hc) (lowGeometry55W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (532745467243574339 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry55W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (1135270931474297357 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry55W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (64 / 125) (145456588095144349 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry55W_hz2 hx hc) (lowGeometry55W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (64 / 125) (627708734184489889 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry55W_hz33 hx hc) (lowGeometry55W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (64 / 125) (627708734184489889 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry55W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry55W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (467254532756425661 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry55W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (218326798381425661 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry55W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (447133283085159753 / 1000000000000000000) (41 / 80) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry55W_hz2 hx hc) (lowGeometry55W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (20062545064062363 / 50000000000000000) (41 / 80) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry55W_hz38 hx hc) (lowGeometry55W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (20062545064062363 / 50000000000000000) (41 / 80) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry55W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry55W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (39 / 80) (61 / 125) θ) :
    OverlapGuard n θ lowWideWindow (358792971 / 1000000000) (709993787 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (23179091 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry55W_hz12 hx hc).2
  have hrp := (lowGeometry55W_hz16 hx hc).2
  have hbn := (lowGeometry55W_hz21 hx hc).2
  have hlo := (lowGeometry55W_hz40 hx hc).1
  have hhi := (lowGeometry55W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry55C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (39 / 80) (61 / 125) θ := hc

theorem lowGeometry55C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry55C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (64 / 125) (41 / 80) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry55C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (156 / 625) (2501 / 10000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry55C_hz0 hx hc) (lowGeometry55C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (2501 / 80000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry55C_hz3 hx hc) (lowGeometry55C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (5591287865957181 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry55C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (32205818107913363 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry55C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (39 / 40) (122 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry55C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry55C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry55C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (1219804784381501 / 40000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry55C_hz7 hx hc) (lowGeometry55C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (7837617214681361 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry55C_hz6 hx hc) (lowGeometry55C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (7837617214681361 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry55C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry55C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (30459 / 4000) (47641 / 6250) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry55C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (47641 / 50000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry55C_hz13 hx hc) (lowGeometry55C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (7956719714681361 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry55C_hz12 hx hc) (lowGeometry55C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (7956719714681361 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry55C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry55C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (61 / 1000000) (θ * x) := bmul (lowGeometry55C_hz0 hx hc) (lowGeometry55C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (61 / 512000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry55C_hz17 hx hc) (lowGeometry55C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (10915155747858113 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry55C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (15717824276915683 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry55C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (15717824276915683 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry55C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry55C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (12753 / 8000) (19947 / 12500) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry55C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry55C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (17841139178875323 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry55C_hz22 hx hc) (lowGeometry55C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry55C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry55C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry55C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry55C_hz26 hx hc) (lowGeometry55C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry55C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 0 (4601757118757059 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry55C_hz24 hx hc) (lowGeometry55C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (515717824276915683 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry55C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B 1 (1063859497107662733 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry55C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (64 / 125) (545227992267677151 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry55C_hz2 hx hc) (lowGeometry55C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (64 / 125) (563635020742705387 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry55C_hz33 hx hc) (lowGeometry55C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (64 / 125) (563635020742705387 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry55C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry55C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (484282175723084317 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry55C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (234529225723084317 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry55C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (480315854280876681 / 1000000000000000000) (41 / 80) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry55C_hz2 hx hc) (lowGeometry55C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (92381765161169689 / 200000000000000000) (41 / 80) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry55C_hz38 hx hc) (lowGeometry55C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry55C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (39 / 80) (61 / 125) θ) : B (92381765161169689 / 200000000000000000) (41 / 80) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry55C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry55C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (39 / 80) (61 / 125) θ) :
    OverlapGuard n θ lowCoreWindow (434266153 / 1000000000) (601339577 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31350469 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry55C_hz12 hx hc).2
  have hrp := (lowGeometry55C_hz16 hx hc).2
  have hbn := (lowGeometry55C_hz21 hx hc).2
  have hlo := (lowGeometry55C_hz40 hx hc).1
  have hhi := (lowGeometry55C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry56W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (61 / 125) (977 / 2000) θ := hc

theorem lowGeometry56W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry56W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (1023 / 2000) (64 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry56W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (62403 / 250000) (3908 / 15625) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry56W_hz0 hx hc) (lowGeometry56W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (977 / 31250000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry56W_hz3 hx hc) (lowGeometry56W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (5591422001602097 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry56W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (16774266004806291 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry56W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (122 / 125) (977 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry56W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry56W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry56W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (977 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry56W_hz7 hx hc) (lowGeometry56W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (28986766004806291 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry56W_hz6 hx hc) (lowGeometry56W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (28986766004806291 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry56W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry56W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (488 / 25) (977 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry56W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (977 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry56W_hz13 hx hc) (lowGeometry56W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (29597391004806291 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry56W_hz12 hx hc) (lowGeometry56W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (29597391004806291 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry56W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry56W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (977 / 16000000) (θ * x) := bmul (lowGeometry56W_hz0 hx hc) (lowGeometry56W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (59689638318671 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry56W_hz17 hx hc) (lowGeometry56W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (2731520600294619 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry56W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (8194561800883857 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry56W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (8194561800883857 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry56W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry56W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (488 / 125) (977 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry56W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry56W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (43692768280345893 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry56W_hz22 hx hc) (lowGeometry56W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry56W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry56W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry56W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry56W_hz26 hx hc) (lowGeometry56W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry56W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (22964696220503333 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry56W_hz24 hx hc) (lowGeometry56W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (133194561800883857 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry56W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (45416425710923441 / 40000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry56W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (1023 / 2000) (116266049819964009 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry56W_hz2 hx hc) (lowGeometry56W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (1023 / 2000) (627259641540826711 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry56W_hz33 hx hc) (lowGeometry56W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (1023 / 2000) (627259641540826711 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry56W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry56W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (116805438199116143 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry56W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (4365923325724013 / 5000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry56W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (446633956221566529 / 1000000000000000000) (64 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry56W_hz2 hx hc) (lowGeometry56W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (400704563780559863 / 1000000000000000000) (64 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry56W_hz38 hx hc) (lowGeometry56W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (400704563780559863 / 1000000000000000000) (64 / 125) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry56W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry56W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (61 / 125) (977 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (358287109 / 1000000000) (709527243 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (23189413 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry56W_hz12 hx hc).2
  have hrp := (lowGeometry56W_hz16 hx hc).2
  have hbn := (lowGeometry56W_hz21 hx hc).2
  have hlo := (lowGeometry56W_hz40 hx hc).1
  have hhi := (lowGeometry56W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry56C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (61 / 125) (977 / 2000) θ := hc

theorem lowGeometry56C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry56C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (1023 / 2000) (64 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry56C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (62403 / 250000) (3908 / 15625) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry56C_hz0 hx hc) (lowGeometry56C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (977 / 31250000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry56C_hz3 hx hc) (lowGeometry56C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (5591422001602097 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry56C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (32206590729228079 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry56C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (122 / 125) (977 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry56C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry56C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry56C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (30526364609137461 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry56C_hz7 hx hc) (lowGeometry56C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (3136647766918277 / 50000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry56C_hz6 hx hc) (lowGeometry56C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (3136647766918277 / 50000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry56C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry56C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (47641 / 6250) (763037 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry56C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (763037 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry56C_hz13 hx hc) (lowGeometry56C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (3184337579418277 / 50000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry56C_hz12 hx hc) (lowGeometry56C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (3184337579418277 / 50000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry56C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry56C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (977 / 16000000) (θ * x) := bmul (lowGeometry56C_hz0 hx hc) (lowGeometry56C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (59689638318671 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry56C_hz17 hx hc) (lowGeometry56C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (2731520600294619 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry56C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (31467117315394011 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry56C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (31467117315394011 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry56C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry56C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (19947 / 12500) (319479 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry56C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry56C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (2232427379323923 / 125000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry56C_hz22 hx hc) (lowGeometry56C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry56C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry56C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry56C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry56C_hz26 hx hc) (lowGeometry56C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry56C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 0 (18425888135351011 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry56C_hz24 hx hc) (lowGeometry56C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (1031467117315394011 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry56C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B 1 (132990551762866099 / 125000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry56C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (1023 / 2000) (272364650010349771 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry56C_hz2 hx hc) (lowGeometry56C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (1023 / 2000) (563155188156050553 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry56C_hz33 hx hc) (lowGeometry56C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (1023 / 2000) (563155188156050553 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry56C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry56C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (968532882684605989 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry56C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (938055944841352747 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry56C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (47981561578635193 / 100000000000000000) (64 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry56C_hz2 hx hc) (lowGeometry56C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (461389727651000919 / 1000000000000000000) (64 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry56C_hz38 hx hc) (lowGeometry56C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry56C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 125) (977 / 2000) θ) : B (461389727651000919 / 1000000000000000000) (64 / 125) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry56C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry56C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (61 / 125) (977 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (86752933 / 200000000) (60084817 / 100000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15683239 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry56C_hz12 hx hc).2
  have hrp := (lowGeometry56C_hz16 hx hc).2
  have hbn := (lowGeometry56C_hz21 hx hc).2
  have hlo := (lowGeometry56C_hz40 hx hc).1
  have hhi := (lowGeometry56C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry57W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (977 / 2000) (489 / 1000) θ := hc

theorem lowGeometry57W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry57W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (511 / 1000) (1023 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry57W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (499247 / 2000000) (500247 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry57W_hz0 hx hc) (lowGeometry57W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (500247 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry57W_hz3 hx hc) (lowGeometry57W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (5591550545242349 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry57W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (16774651635727047 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry57W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (977 / 1000) (489 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry57W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry57W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry57W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (489 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry57W_hz7 hx hc) (lowGeometry57W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (28999651635727047 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry57W_hz6 hx hc) (lowGeometry57W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (28999651635727047 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry57W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry57W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (977 / 50) (489 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry57W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (489 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry57W_hz13 hx hc) (lowGeometry57W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (29610901635727047 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry57W_hz12 hx hc) (lowGeometry57W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (29610901635727047 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry57W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry57W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (489 / 8000000) (θ * x) := bmul (lowGeometry57W_hz0 hx hc) (lowGeometry57W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (119618395303327 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry57W_hz17 hx hc) (lowGeometry57W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (1367127436128207 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry57W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (4101382308384621 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry57W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (4101382308384621 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry57W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry57W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (977 / 250) (489 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry57W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry57W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (43737489639895889 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry57W_hz22 hx hc) (lowGeometry57W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry57W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry57W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry57W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry57W_hz26 hx hc) (lowGeometry57W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry57W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (45976403078100839 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry57W_hz24 hx hc) (lowGeometry57W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (66601382308384621 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry57W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (227110099219845529 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry57W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (511 / 1000) (580834078754754941 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry57W_hz2 hx hc) (lowGeometry57W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (511 / 1000) (31340524091642789 / 50000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry57W_hz33 hx hc) (lowGeometry57W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (511 / 1000) (31340524091642789 / 50000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry57W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry57W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (58398617691615379 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry57W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (8730620283626119 / 10000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry57W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (11153367412332367 / 25000000000000000) (1023 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry57W_hz2 hx hc) (lowGeometry57W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (400158293415193841 / 1000000000000000000) (1023 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry57W_hz38 hx hc) (lowGeometry57W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (400158293415193841 / 1000000000000000000) (1023 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry57W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry57W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (977 / 2000) (489 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (2795167 / 7812500) (354530257 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (115998607 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry57W_hz12 hx hc).2
  have hrp := (lowGeometry57W_hz16 hx hc).2
  have hbn := (lowGeometry57W_hz21 hx hc).2
  have hlo := (lowGeometry57W_hz40 hx hc).1
  have hhi := (lowGeometry57W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry57C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (977 / 2000) (489 / 1000) θ := hc

theorem lowGeometry57C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry57C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (511 / 1000) (1023 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry57C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (499247 / 2000000) (500247 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry57C_hz0 hx hc) (lowGeometry57C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (500247 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry57C_hz3 hx hc) (lowGeometry57C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (5591550545242349 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry57C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (32207331140595931 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry57C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (977 / 1000) (489 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry57C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry57C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry57C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (30557609608737397 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry57C_hz7 hx hc) (lowGeometry57C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (3922808796833333 / 62500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry57C_hz6 hx hc) (lowGeometry57C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (3922808796833333 / 62500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry57C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry57C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (763037 / 100000) (381909 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry57C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (381909 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry57C_hz13 hx hc) (lowGeometry57C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (3982482078083333 / 62500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry57C_hz12 hx hc) (lowGeometry57C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (3982482078083333 / 62500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry57C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry57C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (489 / 8000000) (θ * x) := bmul (lowGeometry57C_hz0 hx hc) (lowGeometry57C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (119618395303327 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry57C_hz17 hx hc) (lowGeometry57C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (1367127436128207 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry57C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (3149861612839389 / 100000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry57C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (3149861612839389 / 100000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry57C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry57C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (319479 / 200000) (159903 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry57C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry57C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (3575539778061489 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry57C_hz22 hx hc) (lowGeometry57C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry57C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry57C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry57C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry57C_hz26 hx hc) (lowGeometry57C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry57C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 0 (9222373897836893 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry57C_hz24 hx hc) (lowGeometry57C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (103149861612839389 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry57C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B 1 (66499337192174481 / 62500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry57C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (511 / 1000) (544230575580755953 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry57C_hz2 hx hc) (lowGeometry57C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (511 / 1000) (562675323376429739 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry57C_hz33 hx hc) (lowGeometry57C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (511 / 1000) (562675323376429739 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry57C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry57C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (96850138387160611 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry57C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (187598986112243227 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry57C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (119828852379195361 / 250000000000000000) (1023 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry57C_hz2 hx hc) (lowGeometry57C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (230435330860553829 / 500000000000000000) (1023 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry57C_hz38 hx hc) (lowGeometry57C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry57C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (977 / 2000) (489 / 1000) θ) : B (230435330860553829 / 500000000000000000) (1023 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry57C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry57C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (977 / 2000) (489 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (433263251 / 1000000000) (24014267 / 40000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62764941 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry57C_hz12 hx hc).2
  have hrp := (lowGeometry57C_hz16 hx hc).2
  have hbn := (lowGeometry57C_hz21 hx hc).2
  have hlo := (lowGeometry57C_hz40 hx hc).1
  have hhi := (lowGeometry57C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry58W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (489 / 1000) (979 / 2000) θ := hc

theorem lowGeometry58W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry58W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (1021 / 2000) (511 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry58W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (499269 / 2000000) (500269 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry58W_hz0 hx hc) (lowGeometry58W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (500269 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry58W_hz3 hx hc) (lowGeometry58W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (1397918374315897 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry58W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (4193755122947691 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry58W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (489 / 500) (979 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry58W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry58W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry58W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (979 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry58W_hz7 hx hc) (lowGeometry58W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (7253130122947691 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry58W_hz6 hx hc) (lowGeometry58W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (7253130122947691 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry58W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry58W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (489 / 25) (979 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry58W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (979 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry58W_hz13 hx hc) (lowGeometry58W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (7406098872947691 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry58W_hz12 hx hc) (lowGeometry58W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (7406098872947691 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry58W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry58W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (979 / 16000000) (θ * x) := bmul (lowGeometry58W_hz0 hx hc) (lowGeometry58W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (59928991185113 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry58W_hz17 hx hc) (lowGeometry58W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (10947967042799591 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry58W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (32843901128398773 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry58W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (32843901128398773 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry58W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry58W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (489 / 125) (979 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry58W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry58W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (8756442199889177 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry58W_hz22 hx hc) (lowGeometry58W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry58W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry58W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry58W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry58W_hz26 hx hc) (lowGeometry58W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry58W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (11505853428798753 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry58W_hz24 hx hc) (lowGeometry58W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (532843901128398773 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry58W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (1135690491878923229 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry58W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (1021 / 2000) (580337841350129771 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry58W_hz2 hx hc) (lowGeometry58W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (1021 / 2000) (626361255065324783 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry58W_hz33 hx hc) (lowGeometry58W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (1021 / 2000) (626361255065324783 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry58W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry58W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (467156098871601227 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry58W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (218234820712933261 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry58W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (222817751947904859 / 500000000000000000) (511 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry58W_hz2 hx hc) (lowGeometry58W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (199806045090307353 / 500000000000000000) (511 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry58W_hz38 hx hc) (lowGeometry58W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (199806045090307353 / 500000000000000000) (511 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry58W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry58W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (489 / 1000) (979 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (178637887 / 500000000) (708593601 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (58025041 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry58W_hz12 hx hc).2
  have hrp := (lowGeometry58W_hz16 hx hc).2
  have hbn := (lowGeometry58W_hz21 hx hc).2
  have hlo := (lowGeometry58W_hz40 hx hc).1
  have hhi := (lowGeometry58W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry58C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (489 / 1000) (979 / 2000) θ := hc

theorem lowGeometry58C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry58C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (1021 / 2000) (511 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry58C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (499269 / 2000000) (500269 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry58C_hz0 hx hc) (lowGeometry58C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (500269 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry58C_hz3 hx hc) (lowGeometry58C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (1397918374315897 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry58C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (32208039344238267 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry58C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (489 / 500) (979 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry58C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry58C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry58C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (30588854608337333 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry58C_hz7 hx hc) (lowGeometry58C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (156992234881439 / 2500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry58C_hz6 hx hc) (lowGeometry58C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (156992234881439 / 2500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry58C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry58C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (381909 / 50000) (764599 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry58C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (764599 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry58C_hz13 hx hc) (lowGeometry58C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (159381606756439 / 2500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry58C_hz12 hx hc) (lowGeometry58C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (159381606756439 / 2500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry58C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry58C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (979 / 16000000) (θ * x) := bmul (lowGeometry58C_hz0 hx hc) (lowGeometry58C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (59928991185113 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry58C_hz17 hx hc) (lowGeometry58C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (10947967042799591 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry58C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (31530145083262823 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry58C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (31530145083262823 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry58C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry58C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (159903 / 100000) (320133 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry58C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry58C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (8947989373011753 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry58C_hz22 hx hc) (lowGeometry58C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry58C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry58C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry58C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry58C_hz26 hx hc) (lowGeometry58C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry58C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 0 (18463607455996561 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry58C_hz24 hx hc) (lowGeometry58C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (1031530145083262823 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry58C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B 1 (1064054440215497249 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry58C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (1021 / 2000) (108746363790023819 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry58C_hz2 hx hc) (lowGeometry58C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (1021 / 2000) (70274428300764457 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry58C_hz33 hx hc) (lowGeometry58C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (1021 / 2000) (70274428300764457 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry58C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry58C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (968469854916737177 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry58C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (234483464970611489 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry58C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (23940761773499433 / 50000000000000000) (511 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry58C_hz2 hx hc) (lowGeometry58C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (460351628013992099 / 1000000000000000000) (511 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry58C_hz38 hx hc) (lowGeometry58C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry58C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (489 / 1000) (979 / 2000) θ) : B (460351628013992099 / 1000000000000000000) (511 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry58C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry58C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (489 / 1000) (979 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (54095239 / 125000000) (599865091 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31398447 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry58C_hz12 hx hc).2
  have hrp := (lowGeometry58C_hz16 hx hc).2
  have hbn := (lowGeometry58C_hz21 hx hc).2
  have hlo := (lowGeometry58C_hz40 hx hc).1
  have hhi := (lowGeometry58C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry59W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (979 / 2000) (49 / 100) θ := hc

theorem lowGeometry59W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry59W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (51 / 100) (1021 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry59W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (49929 / 200000) (50029 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry59W_hz0 hx hc) (lowGeometry59W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (50029 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry59W_hz3 hx hc) (lowGeometry59W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (5591790858034661 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry59W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (16775372574103983 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry59W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (979 / 1000) (49 / 50) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry59W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry59W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry59W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (49 / 1000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry59W_hz7 hx hc) (lowGeometry59W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (29025372574103983 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry59W_hz6 hx hc) (lowGeometry59W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (29025372574103983 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry59W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry59W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (979 / 50) (98 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry59W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (49 / 20000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry59W_hz13 hx hc) (lowGeometry59W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (29637872574103983 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry59W_hz12 hx hc) (lowGeometry59W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (29637872574103983 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry59W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry59W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (49 / 800000) (θ * x) := bmul (lowGeometry59W_hz0 hx hc) (lowGeometry59W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (120098039215687 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry59W_hz17 hx hc) (lowGeometry59W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (219178501879803 / 20000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry59W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (657535505639409 / 10000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry59W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (657535505639409 / 10000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry59W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry59W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (979 / 250) (98 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry59W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry59W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (43826932358995881 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry59W_hz22 hx hc) (lowGeometry59W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry59W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry59W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry59W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry59W_hz26 hx hc) (lowGeometry59W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry59W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (9214084870457837 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry59W_hz24 hx hc) (lowGeometry59W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (10657535505639409 / 10000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry59W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (1135830630539646533 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry59W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (51 / 100) (144960384222622389 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry59W_hz2 hx hc) (lowGeometry59W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (51 / 100) (625911961242778741 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry59W_hz33 hx hc) (lowGeometry59W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (51 / 100) (625911961242778741 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry59W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry59W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (9342464494360591 / 10000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry59W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (218204107070970733 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry59W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (89027275684956059 / 200000000000000000) (1021 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry59W_hz2 hx hc) (lowGeometry59W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (39906595407249111 / 100000000000000000) (1021 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry59W_hz38 hx hc) (lowGeometry59W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (39906595407249111 / 100000000000000000) (1021 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry59W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry59W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (979 / 2000) (49 / 100) θ) :
    OverlapGuard n θ lowWideWindow (178385151 / 500000000) (88515813 / 125000000) ∧ radiusMinus n θ lowWideWindow ≤ (116101491 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry59W_hz12 hx hc).2
  have hrp := (lowGeometry59W_hz16 hx hc).2
  have hbn := (lowGeometry59W_hz21 hx hc).2
  have hlo := (lowGeometry59W_hz40 hx hc).1
  have hhi := (lowGeometry59W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry59C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (979 / 2000) (49 / 100) θ := hc

theorem lowGeometry59C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry59C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (51 / 100) (1021 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry59C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (49929 / 200000) (50029 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry59C_hz0 hx hc) (lowGeometry59C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (50029 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry59C_hz3 hx hc) (lowGeometry59C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (5591790858034661 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry59C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (1006522354446239 / 31250000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry59C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (979 / 1000) (49 / 50) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry59C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry59C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry59C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (30620099607937269 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry59C_hz7 hx hc) (lowGeometry59C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (62828814950216917 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry59C_hz6 hx hc) (lowGeometry59C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (62828814950216917 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry59C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry59C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (764599 / 100000) (38269 / 5000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry59C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (38269 / 40000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry59C_hz13 hx hc) (lowGeometry59C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (63785539950216917 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry59C_hz12 hx hc) (lowGeometry59C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (63785539950216917 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry59C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry59C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (49 / 800000) (θ * x) := bmul (lowGeometry59C_hz0 hx hc) (lowGeometry59C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (120098039215687 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry59C_hz17 hx hc) (lowGeometry59C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (219178501879803 / 20000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry59C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (1972606516918227 / 62500000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry59C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (1972606516918227 / 62500000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry59C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry59C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (320133 / 200000) (16023 / 10000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry59C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry59C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (8957129300869783 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry59C_hz22 hx hc) (lowGeometry59C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry59C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry59C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry59C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry59C_hz26 hx hc) (lowGeometry59C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry59C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 0 (3696493423263867 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry59C_hz24 hx hc) (lowGeometry59C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (64472606516918227 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry59C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B 1 (1064119549717853859 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry59C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (51 / 100) (135808257532741099 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry59C_hz2 hx hc) (lowGeometry59C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (51 / 100) (561715497247283731 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry59C_hz33 hx hc) (lowGeometry59C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (51 / 100) (561715497247283731 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry59C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry59C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (60527393483081773 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry59C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (93787273263508733 / 100000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry59C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (239157546821947269 / 500000000000000000) (1021 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry59C_hz2 hx hc) (lowGeometry59C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (459832626527575203 / 1000000000000000000) (1021 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry59C_hz38 hx hc) (lowGeometry59C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry59C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (979 / 2000) (49 / 100) θ) : B (459832626527575203 / 1000000000000000000) (1021 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry59C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry59C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (979 / 2000) (49 / 100) θ) :
    OverlapGuard n θ lowCoreWindow (432260647 / 1000000000) (599373419 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12565763 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry59C_hz12 hx hc).2
  have hrp := (lowGeometry59C_hz16 hx hc).2
  have hbn := (lowGeometry59C_hz21 hx hc).2
  have hlo := (lowGeometry59C_hz40 hx hc).1
  have hhi := (lowGeometry59C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry60W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (49 / 100) (981 / 2000) θ := hc

theorem lowGeometry60W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry60W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (1019 / 2000) (51 / 100) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (49931 / 200000) (50031 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry60W_hz0 hx hc) (lowGeometry60W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (50031 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry60W_hz3 hx hc) (lowGeometry60W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (5591902627907607 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry60W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (16775707883722821 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry60W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (49 / 50) (981 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry60W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry60W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry60W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (981 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry60W_hz7 hx hc) (lowGeometry60W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (29038207883722821 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry60W_hz6 hx hc) (lowGeometry60W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (29038207883722821 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry60W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry60W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (98 / 5) (981 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry60W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (981 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry60W_hz13 hx hc) (lowGeometry60W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (29651332883722821 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry60W_hz12 hx hc) (lowGeometry60W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (29651332883722821 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry60W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry60W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (981 / 16000000) (θ * x) := bmul (lowGeometry60W_hz0 hx hc) (lowGeometry60W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (7521160451423 / 62500000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry60W_hz17 hx hc) (lowGeometry60W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (10969893674177887 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry60W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (32909681022533661 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry60W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (32909681022533661 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry60W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry60W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (98 / 25) (981 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry60W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry60W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (10967913429636469 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry60W_hz22 hx hc) (lowGeometry60W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry60W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry60W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry60W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry60W_hz26 hx hc) (lowGeometry60W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry60W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (11529358747345839 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry60W_hz24 hx hc) (lowGeometry60W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (532909681022533661 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry60W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (1135970912510154293 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry60W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (1019 / 2000) (57934516538017869 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry60W_hz2 hx hc) (lowGeometry60W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (1019 / 2000) (312731300184781023 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry60W_hz33 hx hc) (lowGeometry60W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (1019 / 2000) (312731300184781023 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry60W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry60W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (467090318977466339 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry60W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (218173366082471251 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry60W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (444637320076076409 / 1000000000000000000) (51 / 100) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry60W_hz2 hx hc) (lowGeometry60W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (398519885086693053 / 1000000000000000000) (51 / 100) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry60W_hz38 hx hc) (lowGeometry60W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (398519885086693053 / 1000000000000000000) (51 / 100) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry60W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry60W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (49 / 100) (981 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (356264961 / 1000000000) (707659223 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (226861 / 1953125) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry60W_hz12 hx hc).2
  have hrp := (lowGeometry60W_hz16 hx hc).2
  have hbn := (lowGeometry60W_hz21 hx hc).2
  have hlo := (lowGeometry60W_hz40 hx hc).1
  have hhi := (lowGeometry60W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry60C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (49 / 100) (981 / 2000) θ := hc

theorem lowGeometry60C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry60C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (1019 / 2000) (51 / 100) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (49931 / 200000) (50031 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry60C_hz0 hx hc) (lowGeometry60C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (50031 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry60C_hz3 hx hc) (lowGeometry60C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (5591902627907607 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry60C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (32209359136747817 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry60C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (49 / 50) (981 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry60C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry60C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry60C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (6130268921507441 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry60C_hz7 hx hc) (lowGeometry60C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (31430351872142511 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry60C_hz6 hx hc) (lowGeometry60C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (31430351872142511 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry60C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry60C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (38269 / 5000) (766161 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry60C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (766161 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry60C_hz13 hx hc) (lowGeometry60C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (31909202497142511 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry60C_hz12 hx hc) (lowGeometry60C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (31909202497142511 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry60C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry60C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (981 / 16000000) (θ * x) := bmul (lowGeometry60C_hz0 hx hc) (lowGeometry60C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (7521160451423 / 62500000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry60C_hz17 hx hc) (lowGeometry60C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (10969893674177887 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry60C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (6318658756326463 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry60C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (6318658756326463 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry60C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry60C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (16023 / 10000) (320787 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry60C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry60C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (17932538457455627 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry60C_hz22 hx hc) (lowGeometry60C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry60C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry60C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry60C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry60C_hz26 hx hc) (lowGeometry60C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry60C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 0 (1850132677664211 / 100000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry60C_hz24 hx hc) (lowGeometry60C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (206318658756326463 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry60C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B 1 (532092361887618579 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry60C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (1019 / 2000) (542734209125370951 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry60C_hz2 hx hc) (lowGeometry60C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (1019 / 2000) (561235535902013061 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry60C_hz33 hx hc) (lowGeometry60C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (1019 / 2000) (561235535902013061 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry60C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry60C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (193681341243673537 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry60C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (937811548648707897 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry60C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (477814984036516673 / 1000000000000000000) (51 / 100) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry60C_hz2 hx hc) (lowGeometry60C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (459313657259874563 / 1000000000000000000) (51 / 100) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry60C_hz38 hx hc) (lowGeometry60C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry60C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (981 / 2000) θ) : B (459313657259874563 / 1000000000000000000) (51 / 100) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry60C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry60C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (49 / 100) (981 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (431759457 / 1000000000) (598881659 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (1964397 / 31250000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry60C_hz12 hx hc).2
  have hrp := (lowGeometry60C_hz16 hx hc).2
  have hbn := (lowGeometry60C_hz21 hx hc).2
  have hlo := (lowGeometry60C_hz40 hx hc).1
  have hhi := (lowGeometry60C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry61W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (981 / 2000) (491 / 1000) θ := hc

theorem lowGeometry61W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry61W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (509 / 1000) (1019 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry61W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (499329 / 2000000) (500329 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry61W_hz0 hx hc) (lowGeometry61W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (500329 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry61W_hz3 hx hc) (lowGeometry61W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (699001100902209 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry61W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (2097003302706627 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry61W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (981 / 1000) (491 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry61W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry61W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry61W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (491 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry61W_hz7 hx hc) (lowGeometry61W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (3631378302706627 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry61W_hz6 hx hc) (lowGeometry61W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (3631378302706627 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry61W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry61W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (981 / 50) (491 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry61W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (491 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry61W_hz13 hx hc) (lowGeometry61W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (3708097052706627 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry61W_hz12 hx hc) (lowGeometry61W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (3708097052706627 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry61W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry61W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (491 / 8000000) (θ * x) := bmul (lowGeometry61W_hz0 hx hc) (lowGeometry61W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (120579567779961 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry61W_hz17 hx hc) (lowGeometry61W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (10980872815034377 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry61W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (32942618445103131 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry61W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (32942618445103131 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry61W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry61W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (981 / 250) (491 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry61W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry61W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (42887085037203 / 976562500000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry61W_hz22 hx hc) (lowGeometry61W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry61W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry61W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry61W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry61W_hz26 hx hc) (lowGeometry61W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry61W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (46164445626477529 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry61W_hz24 hx hc) (lowGeometry61W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (532942618445103131 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry61W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (1136111338220491121 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry61W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (509 / 1000) (578848726823340227 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry61W_hz2 hx hc) (lowGeometry61W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (509 / 1000) (156253293112454439 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry61W_hz33 hx hc) (lowGeometry61W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (509 / 1000) (156253293112454439 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry61W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry61W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (467057381554896869 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry61W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (109071298832458259 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry61W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (44413832884577003 / 100000000000000000) (1019 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry61W_hz2 hx hc) (lowGeometry61W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (397973883219292501 / 1000000000000000000) (1019 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry61W_hz38 hx hc) (lowGeometry61W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (397973883219292501 / 1000000000000000000) (1019 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry61W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry61W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (981 / 2000) (491 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (355759749 / 1000000000) (707191759 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (58102053 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry61W_hz12 hx hc).2
  have hrp := (lowGeometry61W_hz16 hx hc).2
  have hbn := (lowGeometry61W_hz21 hx hc).2
  have hlo := (lowGeometry61W_hz40 hx hc).1
  have hhi := (lowGeometry61W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry61C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (981 / 2000) (491 / 1000) θ := hc

theorem lowGeometry61C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry61C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (509 / 1000) (1019 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry61C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (499329 / 2000000) (500329 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry61C_hz0 hx hc) (lowGeometry61C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (500329 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry61C_hz3 hx hc) (lowGeometry61C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (699001100902209 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry61C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (32209970729573791 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry61C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (981 / 1000) (491 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry61C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry61C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry61C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (30682589607137141 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry61C_hz7 hx hc) (lowGeometry61C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (15723140084177733 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry61C_hz6 hx hc) (lowGeometry61C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (15723140084177733 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry61C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry61C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (766161 / 100000) (383471 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry61C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (383471 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry61C_hz13 hx hc) (lowGeometry61C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (15962809459177733 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry61C_hz12 hx hc) (lowGeometry61C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (15962809459177733 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry61C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry61C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (491 / 8000000) (θ * x) := bmul (lowGeometry61C_hz0 hx hc) (lowGeometry61C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (120579567779961 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry61C_hz17 hx hc) (lowGeometry61C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (10980872815034377 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry61C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (15812456853649503 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry61C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (15812456853649503 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry61C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry61C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (320787 / 200000) (160557 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry61C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry61C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (2243852289146461 / 125000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry61C_hz22 hx hc) (lowGeometry61C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry61C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry61C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry61C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry61C_hz26 hx hc) (lowGeometry61C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry61C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 0 (3704037287392977 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry61C_hz24 hx hc) (lowGeometry61C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (515812456853649503 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry61C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B 1 (1064249962581592121 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry61C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (509 / 1000) (271117677967660593 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry61C_hz2 hx hc) (lowGeometry61C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (509 / 1000) (560755542372286071 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry61C_hz33 hx hc) (lowGeometry61C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (509 / 1000) (560755542372286071 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry61C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry61C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (484187543146350497 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry61C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (14652348558631189 / 15625000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry61C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (119328726661492403 / 250000000000000000) (1019 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry61C_hz2 hx hc) (lowGeometry61C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (458794720209004727 / 1000000000000000000) (1019 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry61C_hz38 hx hc) (lowGeometry61C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry61C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (981 / 2000) (491 / 1000) θ) : B (458794720209004727 / 1000000000000000000) (1019 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry61C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry61C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (981 / 2000) (491 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (431258341 / 1000000000) (59838981 / 100000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62892561 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry61C_hz12 hx hc).2
  have hrp := (lowGeometry61C_hz16 hx hc).2
  have hbn := (lowGeometry61C_hz21 hx hc).2
  have hlo := (lowGeometry61C_hz40 hx hc).1
  have hhi := (lowGeometry61C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry62W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (491 / 1000) (983 / 2000) θ := hc

theorem lowGeometry62W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry62W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (1017 / 2000) (509 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry62W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (499347 / 2000000) (500347 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry62W_hz0 hx hc) (lowGeometry62W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (500347 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry62W_hz3 hx hc) (lowGeometry62W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (5592109396283303 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry62W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (16776328188849909 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry62W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (491 / 500) (983 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry62W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry62W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry62W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (983 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry62W_hz7 hx hc) (lowGeometry62W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (29063828188849909 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry62W_hz6 hx hc) (lowGeometry62W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (29063828188849909 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry62W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry62W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (491 / 25) (983 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry62W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (983 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry62W_hz13 hx hc) (lowGeometry62W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (29678203188849909 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry62W_hz12 hx hc) (lowGeometry62W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (29678203188849909 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry62W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry62W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (983 / 16000000) (θ * x) := bmul (lowGeometry62W_hz0 hx hc) (lowGeometry62W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (6041052114061 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry62W_hz17 hx hc) (lowGeometry62W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (10991862548322737 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry62W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (32975587644968211 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry62W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (32975587644968211 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry62W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry62W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (491 / 125) (983 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry62W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry62W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (10990274109411467 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry62W_hz22 hx hc) (lowGeometry62W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry62W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry62W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry62W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry62W_hz26 hx hc) (lowGeometry62W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry62W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (23105728131785851 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry62W_hz24 hx hc) (lowGeometry62W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (532975587644968211 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry62W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (227250381620399353 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry62W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (1017 / 2000) (289176110611958177 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry62W_hz2 hx hc) (lowGeometry62W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (1017 / 2000) (78070459685936007 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry62W_hz33 hx hc) (lowGeometry62W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (1017 / 2000) (78070459685936007 / 125000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry62W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry62W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (467024412355031789 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry62W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (218111801735562769 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry62W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (27727462795633417 / 62500000000000000) (509 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry62W_hz2 hx hc) (lowGeometry62W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (39742794846656297 / 100000000000000000) (509 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry62W_hz38 hx hc) (lowGeometry62W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (39742794846656297 / 100000000000000000) (509 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry62W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry62W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (491 / 1000) (983 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (355254667 / 1000000000) (70672411 / 100000000) ∧ radiusMinus n θ lowWideWindow ≤ (116255313 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry62W_hz12 hx hc).2
  have hrp := (lowGeometry62W_hz16 hx hc).2
  have hbn := (lowGeometry62W_hz21 hx hc).2
  have hlo := (lowGeometry62W_hz40 hx hc).1
  have hhi := (lowGeometry62W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry62C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (491 / 1000) (983 / 2000) θ := hc

theorem lowGeometry62C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry62C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (1017 / 2000) (509 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry62C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (499347 / 2000000) (500347 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry62C_hz0 hx hc) (lowGeometry62C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (500347 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry62C_hz3 hx hc) (lowGeometry62C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (5592109396283303 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry62C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (16105275061295913 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry62C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (491 / 500) (983 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry62C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry62C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry62C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (30713834606737077 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry62C_hz7 hx hc) (lowGeometry62C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (62924384729328903 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry62C_hz6 hx hc) (lowGeometry62C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (62924384729328903 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry62C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry62C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (383471 / 50000) (767723 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry62C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (767723 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry62C_hz13 hx hc) (lowGeometry62C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (63884038479328903 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry62C_hz12 hx hc) (lowGeometry62C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (63884038479328903 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry62C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry62C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (983 / 16000000) (θ * x) := bmul (lowGeometry62C_hz0 hx hc) (lowGeometry62C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (6041052114061 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry62C_hz17 hx hc) (lowGeometry62C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (10991862548322737 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry62C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (31656564139169483 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry62C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (31656564139169483 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry62C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry62C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (160557 / 100000) (321441 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry62C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry62C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (17969098168887749 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry62C_hz22 hx hc) (lowGeometry62C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry62C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry62C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry62C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry62C_hz26 hx hc) (lowGeometry62C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry62C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 0 (926952304864383 / 50000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry62C_hz24 hx hc) (lowGeometry62C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (1031656564139169483 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry62C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B 1 (532157633165718159 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry62C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (1017 / 2000) (270868235281350543 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry62C_hz2 hx hc) (lowGeometry62C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (1017 / 2000) (280137758329994373 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry62C_hz33 hx hc) (lowGeometry62C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (1017 / 2000) (280137758329994373 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry62C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry62C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (968343435860830517 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry62C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (187537801954951677 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry62C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (238407430735232319 / 500000000000000000) (509 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry62C_hz2 hx hc) (lowGeometry62C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (229137907686588489 / 500000000000000000) (509 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry62C_hz38 hx hc) (lowGeometry62C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry62C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (491 / 1000) (983 / 2000) θ) : B (229137907686588489 / 500000000000000000) (509 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry62C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry62C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (491 / 1000) (983 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (430757299 / 1000000000) (597897873 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12584877 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry62C_hz12 hx hc).2
  have hrp := (lowGeometry62C_hz16 hx hc).2
  have hbn := (lowGeometry62C_hz21 hx hc).2
  have hlo := (lowGeometry62C_hz40 hx hc).1
  have hhi := (lowGeometry62C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry63W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (983 / 2000) (123 / 250) θ := hc

theorem lowGeometry63W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry63W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (127 / 250) (1017 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry63W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (124841 / 500000) (125091 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry63W_hz0 hx hc) (lowGeometry63W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (125091 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry63W_hz3 hx hc) (lowGeometry63W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (5592204395406163 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry63W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (16776613186218489 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry63W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (983 / 1000) (123 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry63W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry63W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry63W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (123 / 2500) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry63W_hz7 hx hc) (lowGeometry63W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (29076613186218489 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry63W_hz6 hx hc) (lowGeometry63W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (29076613186218489 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry63W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry63W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (983 / 50) (492 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry63W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (123 / 50000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry63W_hz13 hx hc) (lowGeometry63W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (29691613186218489 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry63W_hz12 hx hc) (lowGeometry63W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (29691613186218489 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry63W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry63W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (123 / 2000000) (θ * x) := bmul (lowGeometry63W_hz0 hx hc) (lowGeometry63W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (24212598425197 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry63W_hz17 hx hc) (lowGeometry63W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (11002862905897947 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry63W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (33008588717693841 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry63W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (33008588717693841 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry63W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry63W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (983 / 250) (492 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry63W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry63W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (5500727224649483 / 125000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry63W_hz22 hx hc) (lowGeometry63W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry63W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry63W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry63W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry63W_hz26 hx hc) (lowGeometry63W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry63W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (370067735205327 / 8000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry63W_hz24 hx hc) (lowGeometry63W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (533008588717693841 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry63W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (45455704903492433 / 40000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry63W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (127 / 250) (115571129717129511 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry63W_hz2 hx hc) (lowGeometry63W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (127 / 250) (62411411548631343 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry63W_hz33 hx hc) (lowGeometry63W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (127 / 250) (62411411548631343 / 100000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry63W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry63W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (466991411282306159 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry63W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (27260122276430003 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry63W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (27696284232852883 / 62500000000000000) (1017 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry63W_hz2 hx hc) (lowGeometry63W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (396882080824980253 / 1000000000000000000) (1017 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry63W_hz38 hx hc) (lowGeometry63W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (396882080824980253 / 1000000000000000000) (1017 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry63W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry63W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (983 / 2000) (123 / 250) θ) :
    OverlapGuard n θ lowWideWindow (70949943 / 200000000) (353128139 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (116306453 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry63W_hz12 hx hc).2
  have hrp := (lowGeometry63W_hz16 hx hc).2
  have hbn := (lowGeometry63W_hz21 hx hc).2
  have hlo := (lowGeometry63W_hz40 hx hc).1
  have hhi := (lowGeometry63W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry63C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (983 / 2000) (123 / 250) θ := hc

theorem lowGeometry63C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry63C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (127 / 250) (1017 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry63C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (124841 / 500000) (125091 / 500000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry63C_hz0 hx hc) (lowGeometry63C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (125091 / 4000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry63C_hz3 hx hc) (lowGeometry63C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (5592204395406163 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry63C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (32211097317539499 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry63C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (983 / 1000) (123 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry63C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry63C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry63C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (30745079606337013 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry63C_hz7 hx hc) (lowGeometry63C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1967380528871141 / 31250000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry63C_hz6 hx hc) (lowGeometry63C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1967380528871141 / 31250000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry63C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry63C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (767723 / 100000) (96063 / 12500) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry63C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (96063 / 100000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry63C_hz13 hx hc) (lowGeometry63C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1997400216371141 / 31250000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry63C_hz12 hx hc) (lowGeometry63C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1997400216371141 / 31250000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry63C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry63C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (123 / 2000000) (θ * x) := bmul (lowGeometry63C_hz0 hx hc) (lowGeometry63C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (24212598425197 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry63C_hz17 hx hc) (lowGeometry63C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (11002862905897947 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry63C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (3961030646123261 / 125000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry63C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (3961030646123261 / 125000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry63C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry63C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (321441 / 200000) (40221 / 25000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry63C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry63C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (1798737802460381 / 100000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry63C_hz22 hx hc) (lowGeometry63C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry63C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry63C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry63C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry63C_hz26 hx hc) (lowGeometry63C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry63C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 0 (3711581151522087 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry63C_hz24 hx hc) (lowGeometry63C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (128961030646123261 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry63C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B 1 (1064380635219861947 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry63C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (127 / 250) (541237553009299801 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry63C_hz2 hx hc) (lowGeometry63C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (127 / 250) (139948864691727559 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry63C_hz33 hx hc) (lowGeometry63C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (127 / 250) (139948864691727559 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry63C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry63C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (121038969353876739 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry63C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (468813827271958797 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry63C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (476314848508310137 / 1000000000000000000) (1017 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry63C_hz2 hx hc) (lowGeometry63C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (228878471375349851 / 500000000000000000) (1017 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry63C_hz38 hx hc) (lowGeometry63C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry63C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (983 / 2000) (123 / 250) θ) : B (228878471375349851 / 500000000000000000) (1017 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry63C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry63C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (983 / 2000) (123 / 250) θ) :
    OverlapGuard n θ lowCoreWindow (430256331 / 1000000000) (597405847 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62956177 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry63C_hz12 hx hc).2
  have hrp := (lowGeometry63C_hz16 hx hc).2
  have hbn := (lowGeometry63C_hz21 hx hc).2
  have hlo := (lowGeometry63C_hz40 hx hc).1
  have hhi := (lowGeometry63C_hz35 hx hc).2
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
