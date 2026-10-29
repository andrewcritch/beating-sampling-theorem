import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part199 BstLean.Part255 BstLean.Part264b
theorem lowGeometry64W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (123 / 250) (197 / 400) θ := hc

theorem lowGeometry64W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry64W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (203 / 400) (127 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry64W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (24969 / 100000) (25019 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry64W_hz0 hx hc) (lowGeometry64W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (25019 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry64W_hz3 hx hc) (lowGeometry64W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (5592293804871129 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry64W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (16776881414613387 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry64W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (123 / 125) (197 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry64W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry64W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry64W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (197 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry64W_hz7 hx hc) (lowGeometry64W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (29089381414613387 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry64W_hz6 hx hc) (lowGeometry64W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (29089381414613387 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry64W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry64W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (492 / 25) (197 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry64W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (197 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry64W_hz13 hx hc) (lowGeometry64W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (29705006414613387 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry64W_hz12 hx hc) (lowGeometry64W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (29705006414613387 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry64W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry64W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (197 / 3200000) (θ * x) := bmul (lowGeometry64W_hz0 hx hc) (lowGeometry64W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (30326354679803 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry64W_hz17 hx hc) (lowGeometry64W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (11013873919707453 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry64W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (33041621759122359 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry64W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (33041621759122359 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry64W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry64W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (492 / 125) (197 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry64W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry64W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (2202526957837293 / 50000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry64W_hz22 hx hc) (lowGeometry64W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry64W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry64W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry64W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry64W_hz26 hx hc) (lowGeometry64W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry64W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (2894092346110003 / 62500000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry64W_hz24 hx hc) (lowGeometry64W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (533041621759122359 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry64W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (1136533482110381069 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry64W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (203 / 400) (36084938057004599 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry64W_hz2 hx hc) (lowGeometry64W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (203 / 400) (19489515201557301 / 31250000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry64W_hz33 hx hc) (lowGeometry64W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (203 / 400) (19489515201557301 / 31250000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry64W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry64W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (466958378240877641 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry64W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (218050127009350549 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry64W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (221320878914490807 / 500000000000000000) (127 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry64W_hz2 hx hc) (lowGeometry64W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (198168140145610783 / 500000000000000000) (127 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry64W_hz38 hx hc) (lowGeometry64W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (198168140145610783 / 500000000000000000) (127 / 250) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry64W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry64W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (123 / 250) (197 / 400) θ) :
    OverlapGuard n θ lowWideWindow (354244893 / 1000000000) (705788263 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (58178763 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry64W_hz12 hx hc).2
  have hrp := (lowGeometry64W_hz16 hx hc).2
  have hbn := (lowGeometry64W_hz21 hx hc).2
  have hlo := (lowGeometry64W_hz40 hx hc).1
  have hhi := (lowGeometry64W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry64C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (123 / 250) (197 / 400) θ := hc

theorem lowGeometry64C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry64C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (203 / 400) (127 / 250) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry64C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (24969 / 100000) (25019 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry64C_hz0 hx hc) (lowGeometry64C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (25019 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry64C_hz3 hx hc) (lowGeometry64C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (5592293804871129 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry64C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (4026451539507213 / 125000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry64C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (123 / 125) (197 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry64C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry64C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry64C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (30776324605936949 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry64C_hz7 hx hc) (lowGeometry64C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (62987936921994653 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry64C_hz6 hx hc) (lowGeometry64C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (62987936921994653 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry64C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry64C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (96063 / 12500) (153857 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry64C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (153857 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry64C_hz13 hx hc) (lowGeometry64C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (63949543171994653 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry64C_hz12 hx hc) (lowGeometry64C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (63949543171994653 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry64C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry64C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (197 / 3200000) (θ * x) := bmul (lowGeometry64C_hz0 hx hc) (lowGeometry64C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (30326354679803 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry64C_hz17 hx hc) (lowGeometry64C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (11013873919707453 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry64C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (6343991377751493 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry64C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (6343991377751493 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry64C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry64C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (40221 / 25000) (64419 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry64C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry64C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (1800565788031987 / 100000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry64C_hz22 hx hc) (lowGeometry64C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry64C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry64C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry64C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry64C_hz26 hx hc) (lowGeometry64C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry64C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 0 (18576765417933209 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry64C_hz24 hx hc) (lowGeometry64C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (206343991377751493 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry64C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B 1 (1064446069442539563 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry64C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (203 / 400) (540738603276810099 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry64C_hz2 hx hc) (lowGeometry64C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (203 / 400) (139828842173685827 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry64C_hz33 hx hc) (lowGeometry64C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (203 / 400) (139828842173685827 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry64C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry64C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (193656008622248507 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry64C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (468783120943754851 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry64C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (475814867757911173 / 1000000000000000000) (127 / 250) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry64C_hz2 hx hc) (lowGeometry64C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (114309525584994491 / 250000000000000000) (127 / 250) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry64C_hz38 hx hc) (lowGeometry64C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry64C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (123 / 250) (197 / 400) θ) : B (114309525584994491 / 250000000000000000) (127 / 250) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry64C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry64C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (123 / 250) (197 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (214877719 / 500000000) (298456867 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (62987937 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry64C_hz12 hx hc).2
  have hrp := (lowGeometry64C_hz16 hx hc).2
  have hbn := (lowGeometry64C_hz21 hx hc).2
  have hlo := (lowGeometry64C_hz40 hx hc).1
  have hhi := (lowGeometry64C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry65W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (197 / 400) (493 / 1000) θ := hc

theorem lowGeometry65W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry65W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (507 / 1000) (203 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry65W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (99879 / 400000) (100079 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry65W_hz0 hx hc) (lowGeometry65W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (100079 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry65W_hz3 hx hc) (lowGeometry65W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (5592377624946299 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry65W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (16777132874838897 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry65W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (197 / 200) (493 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry65W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry65W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry65W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (493 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry65W_hz7 hx hc) (lowGeometry65W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (29102132874838897 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry65W_hz6 hx hc) (lowGeometry65W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (29102132874838897 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry65W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry65W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (197 / 10) (493 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry65W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (493 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry65W_hz13 hx hc) (lowGeometry65W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (29718382874838897 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry65W_hz12 hx hc) (lowGeometry65W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (29718382874838897 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry65W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry65W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (493 / 8000000) (θ * x) := bmul (lowGeometry65W_hz0 hx hc) (lowGeometry65W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (121548323471401 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry65W_hz17 hx hc) (lowGeometry65W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (689055976361979 / 62500000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry65W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (2067167929085937 / 31250000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry65W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (2067167929085937 / 31250000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry65W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry65W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (197 / 50) (493 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry65W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry65W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (8819052103259171 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry65W_hz22 hx hc) (lowGeometry65W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry65W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry65W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry65W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry65W_hz26 hx hc) (lowGeometry65W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry65W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (2317624408742711 / 50000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry65W_hz24 hx hc) (lowGeometry65W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (33317167929085937 / 31250000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry65W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (227334897421294081 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry65W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (507 / 1000) (576862302206533731 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry65W_hz2 hx hc) (lowGeometry65W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (507 / 1000) (623214790381387951 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry65W_hz33 hx hc) (lowGeometry65W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (507 / 1000) (623214790381387951 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry65W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry65W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (29182832070914063 / 31250000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry65W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (218019248045867617 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry65W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (442143035037019527 / 1000000000000000000) (203 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry65W_hz2 hx hc) (lowGeometry65W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (395790546862165307 / 1000000000000000000) (203 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry65W_hz38 hx hc) (lowGeometry65W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (395790546862165307 / 1000000000000000000) (203 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry65W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry65W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (197 / 400) (493 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (1768701 / 5000000) (5510313 / 7812500) ∧ radiusMinus n θ lowWideWindow ≤ (29102133 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry65W_hz12 hx hc).2
  have hrp := (lowGeometry65W_hz16 hx hc).2
  have hbn := (lowGeometry65W_hz21 hx hc).2
  have hlo := (lowGeometry65W_hz40 hx hc).1
  have hhi := (lowGeometry65W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry65C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (197 / 400) (493 / 1000) θ := hc

theorem lowGeometry65C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry65C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (507 / 1000) (203 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry65C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (99879 / 400000) (100079 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry65C_hz0 hx hc) (lowGeometry65C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (100079 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry65C_hz3 hx hc) (lowGeometry65C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (5592377624946299 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry65C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (32212095119690683 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry65C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (197 / 200) (493 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry65C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry65C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry65C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (6161513921107377 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry65C_hz7 hx hc) (lowGeometry65C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (3938729045326723 / 62500000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry65C_hz6 hx hc) (lowGeometry65C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (3938729045326723 / 62500000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry65C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry65C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (153857 / 20000) (385033 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry65C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (385033 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry65C_hz13 hx hc) (lowGeometry65C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (3998890451576723 / 62500000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry65C_hz12 hx hc) (lowGeometry65C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (3998890451576723 / 62500000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry65C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry65C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (493 / 8000000) (θ * x) := bmul (lowGeometry65C_hz0 hx hc) (lowGeometry65C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (121548323471401 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry65C_hz17 hx hc) (lowGeometry65C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (689055976361979 / 62500000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry65C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (31751699390759993 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry65C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (31751699390759993 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry65C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry65C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (64419 / 40000) (161211 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry65C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry65C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (18023937736035931 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry65C_hz22 hx hc) (lowGeometry65C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry65C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry65C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry65C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry65C_hz26 hx hc) (lowGeometry65C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry65C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 0 (1162226567390999 / 62500000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry65C_hz24 hx hc) (lowGeometry65C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (1031751699390759993 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry65C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B 1 (42580462767828847 / 40000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry65C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (507 / 1000) (540239621366828497 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry65C_hz2 hx hc) (lowGeometry65C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (507 / 1000) (558835246445084481 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry65C_hz33 hx hc) (lowGeometry65C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (507 / 1000) (558835246445084481 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry65C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry65C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (968248300609240007 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry65C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (468752385816340601 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry65C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (475314919217769369 / 1000000000000000000) (203 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry65C_hz2 hx hc) (lowGeometry65C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (91343858827902677 / 200000000000000000) (203 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry65C_hz38 hx hc) (lowGeometry65C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry65C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (197 / 400) (493 / 1000) θ) : B (91343858827902677 / 200000000000000000) (203 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry65C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry65C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (197 / 400) (493 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (214627309 / 500000000) (149105383 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12603933 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry65C_hz12 hx hc).2
  have hrp := (lowGeometry65C_hz16 hx hc).2
  have hbn := (lowGeometry65C_hz21 hx hc).2
  have hlo := (lowGeometry65C_hz40 hx hc).1
  have hhi := (lowGeometry65C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry66W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (493 / 1000) (987 / 2000) θ := hc

theorem lowGeometry66W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry66W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (1013 / 2000) (507 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry66W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (499409 / 2000000) (500409 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry66W_hz0 hx hc) (lowGeometry66W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (500409 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry66W_hz3 hx hc) (lowGeometry66W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (1118491171176599 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry66W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (3355473513529797 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry66W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (493 / 500) (987 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry66W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry66W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry66W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (987 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry66W_hz7 hx hc) (lowGeometry66W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (5822973513529797 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry66W_hz6 hx hc) (lowGeometry66W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (5822973513529797 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry66W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry66W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (493 / 25) (987 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry66W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (987 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry66W_hz13 hx hc) (lowGeometry66W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (5946348513529797 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry66W_hz12 hx hc) (lowGeometry66W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (5946348513529797 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry66W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry66W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (987 / 16000000) (θ * x) := bmul (lowGeometry66W_hz0 hx hc) (lowGeometry66W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (60895853899309 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry66W_hz17 hx hc) (lowGeometry66W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (5517964022142089 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry66W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (16553892066426267 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry66W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (16553892066426267 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry66W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry66W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (493 / 125) (987 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry66W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry66W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (44139981875845851 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry66W_hz22 hx hc) (lowGeometry66W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry66W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry66W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry66W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry66W_hz26 hx hc) (lowGeometry66W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry66W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (5799937351493549 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry66W_hz24 hx hc) (lowGeometry66W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (266553892066426267 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry66W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (227363127602432077 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry66W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (1013 / 2000) (144091382118041329 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry66W_hz2 hx hc) (lowGeometry66W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (1013 / 2000) (155691256821028427 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry66W_hz33 hx hc) (lowGeometry66W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (1013 / 2000) (155691256821028427 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry66W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry66W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (233446107933573733 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry66W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (54497085309333757 / 62500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry66W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (220822189673420383 / 500000000000000000) (507 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry66W_hz2 hx hc) (lowGeometry66W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (197622440267446187 / 500000000000000000) (507 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry66W_hz38 hx hc) (lowGeometry66W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (197622440267446187 / 500000000000000000) (507 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry66W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry66W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (493 / 1000) (987 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (88308909 / 250000000) (704851681 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (116459471 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry66W_hz12 hx hc).2
  have hrp := (lowGeometry66W_hz16 hx hc).2
  have hbn := (lowGeometry66W_hz21 hx hc).2
  have hlo := (lowGeometry66W_hz40 hx hc).1
  have hhi := (lowGeometry66W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry66C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (493 / 1000) (987 / 2000) θ := hc

theorem lowGeometry66C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry66C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (1013 / 2000) (507 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry66C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (499409 / 2000000) (500409 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry66C_hz0 hx hc) (lowGeometry66C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (500409 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry66C_hz3 hx hc) (lowGeometry66C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (1118491171176599 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry66C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (8053136432471513 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry66C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (493 / 500) (987 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry66C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry66C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry66C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (30838814605136821 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry66C_hz7 hx hc) (lowGeometry66C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (63051360335022873 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry66C_hz6 hx hc) (lowGeometry66C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (63051360335022873 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry66C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry66C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (385033 / 50000) (770847 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry66C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (770847 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry66C_hz13 hx hc) (lowGeometry66C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (64014919085022873 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry66C_hz12 hx hc) (lowGeometry66C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (64014919085022873 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry66C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry66C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (987 / 16000000) (θ * x) := bmul (lowGeometry66C_hz0 hx hc) (lowGeometry66C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (60895853899309 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry66C_hz17 hx hc) (lowGeometry66C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (5517964022142089 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry66C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (31783472767538433 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry66C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (31783472767538433 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry66C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry66C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (161211 / 100000) (322749 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry66C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry66C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (2255277198968999 / 125000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry66C_hz22 hx hc) (lowGeometry66C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry66C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry66C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry66C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry66C_hz26 hx hc) (lowGeometry66C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry66C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 0 (465362118464469 / 25000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry66C_hz24 hx hc) (lowGeometry66C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (1031783472767538433 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry66C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B 1 (266144283669060431 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry66C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (1013 / 2000) (107948121456170911 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry66C_hz2 hx hc) (lowGeometry66C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (1013 / 2000) (111671018403886663 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry66C_hz33 hx hc) (lowGeometry66C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (1013 / 2000) (111671018403886663 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry66C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry66C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (968216527232461567 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry66C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (937443243606087991 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry66C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (474815002886483567 / 1000000000000000000) (507 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry66C_hz2 hx hc) (lowGeometry66C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (456200518147904807 / 1000000000000000000) (507 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry66C_hz38 hx hc) (lowGeometry66C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry66C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (493 / 1000) (987 / 2000) θ) : B (456200518147904807 / 1000000000000000000) (507 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry66C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry66C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (493 / 1000) (987 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (428753873 / 1000000000) (297964621 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63051361 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry66C_hz12 hx hc).2
  have hrp := (lowGeometry66C_hz16 hx hc).2
  have hbn := (lowGeometry66C_hz21 hx hc).2
  have hlo := (lowGeometry66C_hz40 hx hc).1
  have hhi := (lowGeometry66C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry67W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (987 / 2000) (247 / 500) θ := hc

theorem lowGeometry67W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry67W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (253 / 500) (1013 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry67W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (249711 / 1000000) (250211 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry67W_hz0 hx hc) (lowGeometry67W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (250211 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry67W_hz3 hx hc) (lowGeometry67W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (5592528497915769 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry67W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (16777585493747307 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry67W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (987 / 1000) (247 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry67W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry67W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry67W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (247 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry67W_hz7 hx hc) (lowGeometry67W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (29127585493747307 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry67W_hz6 hx hc) (lowGeometry67W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (29127585493747307 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry67W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry67W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (987 / 50) (494 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry67W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (247 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry67W_hz13 hx hc) (lowGeometry67W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (29745085493747307 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry67W_hz12 hx hc) (lowGeometry67W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (29745085493747307 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry67W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry67W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (247 / 4000000) (θ * x) := bmul (lowGeometry67W_hz0 hx hc) (lowGeometry67W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (12203557312253 / 100000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry67W_hz17 hx hc) (lowGeometry67W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (11046971219412587 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry67W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (33140913658237761 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry67W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (33140913658237761 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry67W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry67W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (987 / 250) (494 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry67W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry67W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (44184703235395847 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry67W_hz22 hx hc) (lowGeometry67W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry67W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry67W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry67W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry67W_hz26 hx hc) (lowGeometry67W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry67W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (9289301889808513 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry67W_hz24 hx hc) (lowGeometry67W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (533140913658237761 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry67W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (9095655482122897 / 8000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry67W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (253 / 500) (575868687711905917 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry67W_hz2 hx hc) (lowGeometry67W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (253 / 500) (311157598580474241 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry67W_hz33 hx hc) (lowGeometry67W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (253 / 500) (311157598580474241 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry67W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry67W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (466859086341762239 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry67W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (217957406499865009 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry67W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (220572895377863389 / 500000000000000000) (1013 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry67W_hz2 hx hc) (lowGeometry67W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (394699281306684213 / 1000000000000000000) (1013 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry67W_hz38 hx hc) (lowGeometry67W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (394699281306684213 / 1000000000000000000) (1013 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry67W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry67W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (987 / 2000) (247 / 500) θ) :
    OverlapGuard n θ lowWideWindow (176365601 / 500000000) (140876623 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (58255171 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry67W_hz12 hx hc).2
  have hrp := (lowGeometry67W_hz16 hx hc).2
  have hbn := (lowGeometry67W_hz21 hx hc).2
  have hlo := (lowGeometry67W_hz40 hx hc).1
  have hhi := (lowGeometry67W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry67C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (987 / 2000) (247 / 500) θ := hc

theorem lowGeometry67C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry67C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (253 / 500) (1013 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry67C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (249711 / 1000000) (250211 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry67C_hz0 hx hc) (lowGeometry67C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (250211 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry67C_hz3 hx hc) (lowGeometry67C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (5592528497915769 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry67C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (3221296414799483 / 100000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry67C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (987 / 1000) (247 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry67C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry67C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry67C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (30870059604736757 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry67C_hz7 hx hc) (lowGeometry67C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (63083023752731587 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry67C_hz6 hx hc) (lowGeometry67C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (63083023752731587 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry67C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry67C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (770847 / 100000) (192907 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry67C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (192907 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry67C_hz13 hx hc) (lowGeometry67C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (64047558752731587 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry67C_hz12 hx hc) (lowGeometry67C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (64047558752731587 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry67C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry67C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (247 / 4000000) (θ * x) := bmul (lowGeometry67C_hz0 hx hc) (lowGeometry67C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (12203557312253 / 100000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry67C_hz17 hx hc) (lowGeometry67C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (11046971219412587 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry67C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (31815277111908251 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry67C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (31815277111908251 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry67C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry67C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (322749 / 200000) (80769 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry67C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry67C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (18060497447468053 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry67C_hz22 hx hc) (lowGeometry67C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry67C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry67C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry67C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry67C_hz26 hx hc) (lowGeometry67C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry67C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 0 (3726668879780307 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry67C_hz24 hx hc) (lowGeometry67C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (1031815277111908251 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry67C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B 1 (66540172880095251 / 62500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry67C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (253 / 500) (107848312204058383 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry67C_hz2 hx hc) (lowGeometry67C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (253 / 500) (11157498108383869 / 20000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry67C_hz33 hx hc) (lowGeometry67C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (253 / 500) (11157498108383869 / 20000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry67C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry67C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (968184722888091749 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry67C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (937381657633891011 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry67C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (474315118762748851 / 1000000000000000000) (1013 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry67C_hz2 hx hc) (lowGeometry67C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (113920443590961829 / 250000000000000000) (1013 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry67C_hz38 hx hc) (lowGeometry67C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry67C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (987 / 2000) (247 / 500) θ) : B (113920443590961829 / 250000000000000000) (1013 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry67C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry67C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (987 / 2000) (247 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (214126601 / 500000000) (9303701 / 15625000) ∧ radiusMinus n θ lowCoreWindow ≤ (3942689 / 62500000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry67C_hz12 hx hc).2
  have hrp := (lowGeometry67C_hz16 hx hc).2
  have hbn := (lowGeometry67C_hz21 hx hc).2
  have hlo := (lowGeometry67C_hz40 hx hc).1
  have hhi := (lowGeometry67C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry68W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (247 / 500) (989 / 2000) θ := hc

theorem lowGeometry68W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry68W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (1011 / 2000) (253 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry68W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (249717 / 1000000) (250217 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry68W_hz0 hx hc) (lowGeometry68W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (250217 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry68W_hz3 hx hc) (lowGeometry68W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (2796297775631201 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry68W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (8388893326893603 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry68W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (247 / 250) (989 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry68W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry68W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry68W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (989 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry68W_hz7 hx hc) (lowGeometry68W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (14570143326893603 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry68W_hz6 hx hc) (lowGeometry68W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (14570143326893603 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry68W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry68W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (494 / 25) (989 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry68W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (989 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry68W_hz13 hx hc) (lowGeometry68W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (14879205826893603 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry68W_hz12 hx hc) (lowGeometry68W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (14879205826893603 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry68W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry68W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (989 / 16000000) (θ * x) := bmul (lowGeometry68W_hz0 hx hc) (lowGeometry68W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (61139960435213 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry68W_hz17 hx hc) (lowGeometry68W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (2764506294874661 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry68W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (8293518884623983 / 125000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry68W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (8293518884623983 / 125000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry68W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry68W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (494 / 125) (989 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry68W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry68W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (44229424594945843 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry68W_hz22 hx hc) (lowGeometry68W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry68W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry68W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry68W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry68W_hz26 hx hc) (lowGeometry68W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry68W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (23246760043068369 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry68W_hz24 hx hc) (lowGeometry68W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (133293518884623983 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry68W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (227419675861063813 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry68W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (1011 / 2000) (575371779928491447 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry68W_hz2 hx hc) (lowGeometry68W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (1011 / 2000) (124373060002925637 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry68W_hz33 hx hc) (lowGeometry68W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (1011 / 2000) (124373060002925637 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry68W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry68W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (116706481115376017 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry68W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (108963221874668951 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry68W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (440647269261161237 / 1000000000000000000) (253 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry68W_hz2 hx hc) (lowGeometry68W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (394153749175024499 / 1000000000000000000) (253 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry68W_hz38 hx hc) (lowGeometry68W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (394153749175024499 / 1000000000000000000) (253 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry68W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry68W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (247 / 500) (989 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (352226897 / 1000000000) (351957183 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (116561147 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry68W_hz12 hx hc).2
  have hrp := (lowGeometry68W_hz16 hx hc).2
  have hbn := (lowGeometry68W_hz21 hx hc).2
  have hlo := (lowGeometry68W_hz40 hx hc).1
  have hhi := (lowGeometry68W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry68C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (247 / 500) (989 / 2000) θ := hc

theorem lowGeometry68C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry68C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (1011 / 2000) (253 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry68C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (249717 / 1000000) (250217 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry68C_hz0 hx hc) (lowGeometry68C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (250217 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry68C_hz3 hx hc) (lowGeometry68C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (2796297775631201 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry68C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (8053337593817859 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry68C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (247 / 250) (989 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry68C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry68C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry68C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (30901304604336693 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry68C_hz7 hx hc) (lowGeometry68C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (63114654979608129 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry68C_hz6 hx hc) (lowGeometry68C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (63114654979608129 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry68C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry68C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (192907 / 25000) (772409 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry68C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (772409 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry68C_hz13 hx hc) (lowGeometry68C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (64080166229608129 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry68C_hz12 hx hc) (lowGeometry68C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (64080166229608129 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry68C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry68C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (989 / 16000000) (θ * x) := bmul (lowGeometry68C_hz0 hx hc) (lowGeometry68C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (61139960435213 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry68C_hz17 hx hc) (lowGeometry68C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (2764506294874661 / 250000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry68C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (6369422503391219 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry68C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (6369422503391219 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry68C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry68C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (80769 / 50000) (323403 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry68C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry68C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (9039388651592057 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry68C_hz22 hx hc) (lowGeometry68C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry68C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry68C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry68C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry68C_hz26 hx hc) (lowGeometry68C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry68C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 0 (1865220405922431 / 100000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry68C_hz24 hx hc) (lowGeometry68C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (206369422503391219 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry68C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B 1 (266177115902394963 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry68C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (1011 / 2000) (269371241293223703 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry68C_hz2 hx hc) (lowGeometry68C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (1011 / 2000) (139348671661417929 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry68C_hz33 hx hc) (lowGeometry68C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (1011 / 2000) (139348671661417929 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry68C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry68C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (193630577496608781 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry68C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (937320013541755471 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry68C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (47381526684535739 / 100000000000000000) (253 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry68C_hz2 hx hc) (lowGeometry68C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (11379076569653327 / 25000000000000000) (253 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry68C_hz38 hx hc) (lowGeometry68C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry68C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (247 / 500) (989 / 2000) θ) : B (11379076569653327 / 25000000000000000) (253 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry68C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry68C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (247 / 500) (989 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (106938151 / 250000000) (594944397 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12622931 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry68C_hz12 hx hc).2
  have hrp := (lowGeometry68C_hz16 hx hc).2
  have hbn := (lowGeometry68C_hz21 hx hc).2
  have hlo := (lowGeometry68C_hz40 hx hc).1
  have hhi := (lowGeometry68C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry69W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (989 / 2000) (99 / 200) θ := hc

theorem lowGeometry69W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry69W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (101 / 200) (1011 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry69W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (99889 / 400000) (100089 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry69W_hz0 hx hc) (lowGeometry69W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (100089 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry69W_hz3 hx hc) (lowGeometry69W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (5592657016123911 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry69W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (16777971048371733 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry69W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (989 / 1000) (99 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry69W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry69W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry69W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (99 / 2000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry69W_hz7 hx hc) (lowGeometry69W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (29152971048371733 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry69W_hz6 hx hc) (lowGeometry69W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (29152971048371733 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry69W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry69W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (989 / 50) (99 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry69W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (99 / 40000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry69W_hz13 hx hc) (lowGeometry69W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (29771721048371733 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry69W_hz12 hx hc) (lowGeometry69W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (29771721048371733 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry69W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry69W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (99 / 1600000) (θ * x) := bmul (lowGeometry69W_hz0 hx hc) (lowGeometry69W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (7657797029703 / 62500000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry69W_hz17 hx hc) (lowGeometry69W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (11069089956958883 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry69W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (33207269870876649 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry69W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (33207269870876649 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry69W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry69W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (989 / 250) (99 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry69W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry69W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (44274145954495839 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry69W_hz22 hx hc) (lowGeometry69W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry69W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry69W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry69W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry69W_hz26 hx hc) (lowGeometry69W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry69W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (46540530723230911 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry69W_hz24 hx hc) (lowGeometry69W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (533207269870876649 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry69W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (45489598822904621 / 40000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry69W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (101 / 200) (143718701281114287 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry69W_hz2 hx hc) (lowGeometry69W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (101 / 200) (621415335847688059 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry69W_hz33 hx hc) (lowGeometry69W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (101 / 200) (621415335847688059 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry69W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry69W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (466792730129123351 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry69W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (217895452901400583 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry69W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (440148814860829177 / 1000000000000000000) (1011 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry69W_hz2 hx hc) (lowGeometry69W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (196804142068799133 / 500000000000000000) (1011 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry69W_hz38 hx hc) (lowGeometry69W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (196804142068799133 / 500000000000000000) (1011 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry69W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry69W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (989 / 2000) (99 / 200) θ) :
    OverlapGuard n θ lowWideWindow (351722721 / 1000000000) (351722717 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (23322377 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry69W_hz12 hx hc).2
  have hrp := (lowGeometry69W_hz16 hx hc).2
  have hbn := (lowGeometry69W_hz21 hx hc).2
  have hlo := (lowGeometry69W_hz40 hx hc).1
  have hhi := (lowGeometry69W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry69C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (989 / 2000) (99 / 200) θ := hc

theorem lowGeometry69C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry69C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (101 / 200) (1011 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry69C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (99889 / 400000) (100089 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry69C_hz0 hx hc) (lowGeometry69C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (100089 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry69C_hz3 hx hc) (lowGeometry69C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (5592657016123911 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry69C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (31458695715697 / 976562500000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry69C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (989 / 1000) (99 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry69C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry69C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry69C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (30932549603936629 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry69C_hz7 hx hc) (lowGeometry69C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (63146254016810357 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry69C_hz6 hx hc) (lowGeometry69C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (63146254016810357 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry69C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry69C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (772409 / 100000) (77319 / 10000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry69C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (77319 / 80000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry69C_hz13 hx hc) (lowGeometry69C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (64112741516810357 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry69C_hz12 hx hc) (lowGeometry69C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (64112741516810357 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry69C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry69C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (99 / 1600000) (θ * x) := bmul (lowGeometry69C_hz0 hx hc) (lowGeometry69C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (7657797029703 / 62500000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry69C_hz17 hx hc) (lowGeometry69C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (11069089956958883 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry69C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (1992436192252599 / 62500000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry69C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (1992436192252599 / 62500000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry69C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry69C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (323403 / 200000) (32373 / 20000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry69C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry69C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (9048528579450087 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry69C_hz22 hx hc) (lowGeometry69C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry69C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry69C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry69C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry69C_hz26 hx hc) (lowGeometry69C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry69C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 0 (4667765929886771 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry69C_hz24 hx hc) (lowGeometry69C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (64492436192252599 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry69C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B 1 (532387113729506933 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry69C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (101 / 200) (53824337198053151 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry69C_hz2 hx hc) (lowGeometry69C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (101 / 200) (278457217850039297 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry69C_hz33 hx hc) (lowGeometry69C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (101 / 200) (278457217850039297 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry69C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry69C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (60507563807747401 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry69C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (937258311154847529 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry69C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (236657723566599001 / 500000000000000000) (1011 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry69C_hz2 hx hc) (lowGeometry69C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (227322191706825459 / 500000000000000000) (1011 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry69C_hz38 hx hc) (lowGeometry69C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry69C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (989 / 2000) (99 / 200) θ) : B (227322191706825459 / 500000000000000000) (1011 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry69C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry69C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (989 / 2000) (99 / 200) θ) :
    OverlapGuard n θ lowCoreWindow (427252081 / 1000000000) (594451843 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (12629251 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry69C_hz12 hx hc).2
  have hrp := (lowGeometry69C_hz16 hx hc).2
  have hbn := (lowGeometry69C_hz21 hx hc).2
  have hlo := (lowGeometry69C_hz40 hx hc).1
  have hhi := (lowGeometry69C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry70W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (99 / 200) (991 / 2000) θ := hc

theorem lowGeometry70W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry70W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (1009 / 2000) (101 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry70W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (99891 / 400000) (100091 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry70W_hz0 hx hc) (lowGeometry70W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (100091 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry70W_hz3 hx hc) (lowGeometry70W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (699089111585569 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry70W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (2097267334756707 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry70W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (99 / 100) (991 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry70W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry70W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry70W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (991 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry70W_hz7 hx hc) (lowGeometry70W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (3645704834756707 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry70W_hz6 hx hc) (lowGeometry70W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (3645704834756707 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry70W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry70W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (99 / 5) (991 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry70W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (991 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry70W_hz13 hx hc) (lowGeometry70W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (3723126709756707 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry70W_hz12 hx hc) (lowGeometry70W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (3723126709756707 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry70W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry70W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (991 / 16000000) (θ * x) := bmul (lowGeometry70W_hz0 hx hc) (lowGeometry70W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (6138503468781 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry70W_hz17 hx hc) (lowGeometry70W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (5540082792152569 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry70W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (16620248376457707 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry70W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (16620248376457707 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry70W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry70W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (99 / 25) (991 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry70W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry70W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (22159433657022917 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry70W_hz22 hx hc) (lowGeometry70W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry70W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry70W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry70W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry70W_hz26 hx hc) (lowGeometry70W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry70W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (46587541360325083 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry70W_hz24 hx hc) (lowGeometry70W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (266620248376457707 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry70W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (1137381709509183977 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry70W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (1009 / 2000) (574377763302137909 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry70W_hz2 hx hc) (lowGeometry70W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (1009 / 2000) (38810331541403937 / 62500000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry70W_hz33 hx hc) (lowGeometry70W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (1009 / 2000) (38810331541403937 / 62500000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry70W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry70W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (233379751623542293 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry70W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (108932216935732583 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry70W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (1717384482627409 / 3906250000000000) (101 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry70W_hz2 hx hc) (lowGeometry70W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (393062886192291621 / 1000000000000000000) (101 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry70W_hz38 hx hc) (lowGeometry70W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (393062886192291621 / 1000000000000000000) (101 / 200) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry70W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry70W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (99 / 200) (991 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (175609337 / 500000000) (351488159 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (23332511 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry70W_hz12 hx hc).2
  have hrp := (lowGeometry70W_hz16 hx hc).2
  have hbn := (lowGeometry70W_hz21 hx hc).2
  have hlo := (lowGeometry70W_hz40 hx hc).1
  have hhi := (lowGeometry70W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry70C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (99 / 200) (991 / 2000) θ := hc

theorem lowGeometry70C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry70C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (1009 / 2000) (101 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry70C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (99891 / 400000) (100091 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry70C_hz0 hx hc) (lowGeometry70C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (100091 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry70C_hz3 hx hc) (lowGeometry70C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (699089111585569 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry70C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (1610701313093151 / 50000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry70C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (99 / 100) (991 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry70C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry70C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry70C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (6192758920707313 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry70C_hz7 hx hc) (lowGeometry70C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (12635564173079917 / 200000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry70C_hz6 hx hc) (lowGeometry70C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (12635564173079917 / 200000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry70C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry70C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (77319 / 10000) (773971 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry70C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (773971 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry70C_hz13 hx hc) (lowGeometry70C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (12829056923079917 / 200000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry70C_hz12 hx hc) (lowGeometry70C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (12829056923079917 / 200000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry70C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry70C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (991 / 16000000) (θ * x) := bmul (lowGeometry70C_hz0 hx hc) (lowGeometry70C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (6138503468781 / 50000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry70C_hz17 hx hc) (lowGeometry70C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (5540082792152569 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry70C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (15955438441399399 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry70C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (15955438441399399 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry70C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry70C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (32373 / 20000) (324057 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry70C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry70C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (3623067402923247 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry70C_hz22 hx hc) (lowGeometry70C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry70C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry70C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry70C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry70C_hz26 hx hc) (lowGeometry70C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry70C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 0 (18689923379869859 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry70C_hz24 hx hc) (lowGeometry70C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (515955438441399399 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry70C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B 1 (1064840057829026739 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry70C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (1009 / 2000) (67218028650457313 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry70C_hz2 hx hc) (lowGeometry70C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (1009 / 2000) (556434152583528363 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry70C_hz33 hx hc) (lowGeometry70C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (1009 / 2000) (556434152583528363 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry70C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry70C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (484044561558600601 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry70C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (468598275148915773 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry70C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (236407829812628007 / 500000000000000000) (101 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry70C_hz2 hx hc) (lowGeometry70C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (90825147249077231 / 200000000000000000) (101 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry70C_hz38 hx hc) (lowGeometry70C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry70C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (99 / 200) (991 / 2000) θ) : B (90825147249077231 / 200000000000000000) (101 / 200) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry70C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry70C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (99 / 200) (991 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (426751631 / 1000000000) (593959201 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63177821 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry70C_hz12 hx hc).2
  have hrp := (lowGeometry70C_hz16 hx hc).2
  have hbn := (lowGeometry70C_hz21 hx hc).2
  have hlo := (lowGeometry70C_hz40 hx hc).1
  have hhi := (lowGeometry70C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry71W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (991 / 2000) (62 / 125) θ := hc

theorem lowGeometry71W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry71W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (63 / 125) (1009 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry71W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (62433 / 250000) (31279 / 125000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry71W_hz0 hx hc) (lowGeometry71W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (31279 / 1000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry71W_hz3 hx hc) (lowGeometry71W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (279638159055591 / 50000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry71W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (838914477166773 / 12500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry71W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (991 / 1000) (124 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry71W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry71W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry71W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (31 / 625) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry71W_hz7 hx hc) (lowGeometry71W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1458914477166773 / 12500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry71W_hz6 hx hc) (lowGeometry71W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1458914477166773 / 12500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry71W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry71W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (991 / 50) (496 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry71W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (31 / 12500) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry71W_hz13 hx hc) (lowGeometry71W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1489914477166773 / 12500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry71W_hz12 hx hc) (lowGeometry71W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1489914477166773 / 12500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry71W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry71W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (31 / 500000) (θ * x) := bmul (lowGeometry71W_hz0 hx hc) (lowGeometry71W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (61507936507937 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry71W_hz17 hx hc) (lowGeometry71W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (11091252094144917 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry71W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (33273756282434751 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry71W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (33273756282434751 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry71W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry71W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (991 / 250) (496 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry71W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry71W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (4436358867359583 / 100000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry71W_hz22 hx hc) (lowGeometry71W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry71W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry71W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry71W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry71W_hz26 hx hc) (lowGeometry71W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry71W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (5829318999677407 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry71W_hz24 hx hc) (lowGeometry71W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (533273756282434751 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry71W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (1137523596558310469 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry71W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (63 / 125) (35867540903979227 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry71W_hz2 hx hc) (lowGeometry71W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (63 / 125) (77564400807635861 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry71W_hz33 hx hc) (lowGeometry71W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (63 / 125) (77564400807635861 / 125000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry71W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry71W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (466726243717565249 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry71W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (43566677314941623 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry71W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (439152107334611559 / 1000000000000000000) (1009 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry71W_hz2 hx hc) (lowGeometry71W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (392517555337192303 / 1000000000000000000) (1009 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry71W_hz38 hx hc) (lowGeometry71W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (392517555337192303 / 1000000000000000000) (1009 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry71W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry71W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (991 / 2000) (62 / 125) θ) :
    OverlapGuard n θ lowWideWindow (70142951 / 200000000) (35125351 / 50000000) ∧ radiusMinus n θ lowWideWindow ≤ (116713159 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry71W_hz12 hx hc).2
  have hrp := (lowGeometry71W_hz16 hx hc).2
  have hbn := (lowGeometry71W_hz21 hx hc).2
  have hlo := (lowGeometry71W_hz40 hx hc).1
  have hhi := (lowGeometry71W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry71C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (991 / 2000) (62 / 125) θ := hc

theorem lowGeometry71C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry71C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (63 / 125) (1009 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry71C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (62433 / 250000) (31279 / 125000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry71C_hz0 hx hc) (lowGeometry71C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (31279 / 1000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry71C_hz3 hx hc) (lowGeometry71C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (279638159055591 / 50000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry71C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (8053578980801021 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry71C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (991 / 1000) (124 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry71C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry71C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry71C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (30995039603136501 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry71C_hz7 hx hc) (lowGeometry71C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (12641871105268117 / 200000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry71C_hz6 hx hc) (lowGeometry71C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (12641871105268117 / 200000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry71C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry71C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (773971 / 100000) (24211 / 3125) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry71C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (24211 / 25000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry71C_hz13 hx hc) (lowGeometry71C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (12835559105268117 / 200000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry71C_hz12 hx hc) (lowGeometry71C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (12835559105268117 / 200000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry71C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry71C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (31 / 500000) (θ * x) := bmul (lowGeometry71C_hz0 hx hc) (lowGeometry71C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (61507936507937 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry71C_hz17 hx hc) (lowGeometry71C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (11091252094144917 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry71C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (31942806031137361 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry71C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (31942806031137361 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry71C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry71C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (324057 / 200000) (10137 / 6250) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry71C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry71C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (2266702108791537 / 125000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry71C_hz22 hx hc) (lowGeometry71C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry71C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry71C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry71C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry71C_hz26 hx hc) (lowGeometry71C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry71C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 0 (9354391520096317 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry71C_hz24 hx hc) (lowGeometry71C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (1031942806031137361 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry71C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B 1 (266226488729854397 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry71C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (63 / 125) (268622527128423087 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry71C_hz2 hx hc) (lowGeometry71C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (63 / 125) (69494229662129851 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry71C_hz33 hx hc) (lowGeometry71C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (63 / 125) (69494229662129851 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry71C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry71C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (968057193968862639 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry71C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (937134730794868143 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry71C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (59039488040076693 / 125000000000000000) (1009 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry71C_hz2 hx hc) (lowGeometry71C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (45360712128042091 / 100000000000000000) (1009 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry71C_hz38 hx hc) (lowGeometry71C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry71C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (991 / 2000) (62 / 125) θ) : B (45360712128042091 / 100000000000000000) (1009 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry71C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry71C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (991 / 2000) (62 / 125) θ) :
    OverlapGuard n θ lowCoreWindow (85250251 / 200000000) (593466471 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15802339 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry71C_hz12 hx hc).2
  have hrp := (lowGeometry71C_hz16 hx hc).2
  have hbn := (lowGeometry71C_hz21 hx hc).2
  have hlo := (lowGeometry71C_hz40 hx hc).1
  have hhi := (lowGeometry71C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry72W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (62 / 125) (993 / 2000) θ := hc

theorem lowGeometry72W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry72W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (1007 / 2000) (63 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry72W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (31217 / 125000) (62559 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry72W_hz0 hx hc) (lowGeometry72W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (62559 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry72W_hz3 hx hc) (lowGeometry72W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (1118561576311291 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry72W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (3355684728933873 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry72W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (124 / 125) (993 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry72W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry72W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry72W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (993 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry72W_hz7 hx hc) (lowGeometry72W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (5838184728933873 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry72W_hz6 hx hc) (lowGeometry72W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (5838184728933873 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry72W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry72W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (496 / 25) (993 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry72W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (993 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry72W_hz13 hx hc) (lowGeometry72W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (5962309728933873 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry72W_hz12 hx hc) (lowGeometry72W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (5962309728933873 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry72W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry72W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (993 / 16000000) (θ * x) := bmul (lowGeometry72W_hz0 hx hc) (lowGeometry72W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (61631082423039 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry72W_hz17 hx hc) (lowGeometry72W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (17763759230691 / 1600000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry72W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (53291277692073 / 800000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry72W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (53291277692073 / 800000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry72W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry72W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (496 / 125) (993 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry72W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry72W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (22204155016572913 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry72W_hz22 hx hc) (lowGeometry72W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry72W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry72W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry72W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry72W_hz26 hx hc) (lowGeometry72W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry72W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (11670390658628357 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry72W_hz24 hx hc) (lowGeometry72W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (853291277692073 / 800000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry72W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (1137665632164641309 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry72W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (1007 / 2000) (28669173930548961 / 50000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry72W_hz2 hx hc) (lowGeometry72W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (1007 / 2000) (77508130155686581 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry72W_hz33 hx hc) (lowGeometry72W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (1007 / 2000) (77508130155686581 / 125000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry72W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry72W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (746708722307927 / 800000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry72W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (217802310926069077 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry72W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (438653854205103121 / 1000000000000000000) (63 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry72W_hz2 hx hc) (lowGeometry72W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (391972291570589693 / 1000000000000000000) (63 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry72W_hz38 hx hc) (lowGeometry72W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (391972291570589693 / 1000000000000000000) (63 / 125) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry72W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry72W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (62 / 125) (993 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (175105483 / 500000000) (351018769 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (23352739 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry72W_hz12 hx hc).2
  have hrp := (lowGeometry72W_hz16 hx hc).2
  have hbn := (lowGeometry72W_hz21 hx hc).2
  have hlo := (lowGeometry72W_hz40 hx hc).1
  have hhi := (lowGeometry72W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry72C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (62 / 125) (993 / 2000) θ := hc

theorem lowGeometry72C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry72C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (1007 / 2000) (63 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry72C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (31217 / 125000) (62559 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry72C_hz0 hx hc) (lowGeometry72C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (62559 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry72C_hz3 hx hc) (lowGeometry72C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (1118561576311291 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry72C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (32214573397765181 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry72C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (124 / 125) (993 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry72C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry72C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry72C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (31026284602736437 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry72C_hz7 hx hc) (lowGeometry72C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (31620429000250809 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry72C_hz6 hx hc) (lowGeometry72C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (31620429000250809 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry72C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry72C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (24211 / 3125) (775533 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry72C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (775533 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry72C_hz13 hx hc) (lowGeometry72C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (32105137125250809 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry72C_hz12 hx hc) (lowGeometry72C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (32105137125250809 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry72C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry72C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (993 / 16000000) (θ * x) := bmul (lowGeometry72C_hz0 hx hc) (lowGeometry72C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (61631082423039 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry72C_hz17 hx hc) (lowGeometry72C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (17763759230691 / 1600000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry72C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (159873833076219 / 5000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry72C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (159873833076219 / 5000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry72C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry72C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (10137 / 6250) (324711 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry72C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry72C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (18151896726048357 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry72C_hz22 hx hc) (lowGeometry72C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry72C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry72C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry72C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry72C_hz26 hx hc) (lowGeometry72C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry72C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 0 (18727642700515409 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry72C_hz24 hx hc) (lowGeometry72C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (5159873833076219 / 5000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry72C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B 1 (106497191893058691 / 100000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry72C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (1007 / 2000) (536745847141015803 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry72C_hz2 hx hc) (lowGeometry72C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (1007 / 2000) (138868372460382803 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry72C_hz33 hx hc) (lowGeometry72C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (1007 / 2000) (138868372460382803 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry72C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry72C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (4840126166923781 / 5000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry72C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (937072852469611709 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry72C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (94363236243689899 / 200000000000000000) (63 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry72C_hz2 hx hc) (lowGeometry72C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (226544269258967043 / 500000000000000000) (63 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry72C_hz38 hx hc) (lowGeometry72C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry72C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (62 / 125) (993 / 2000) θ) : B (226544269258967043 / 500000000000000000) (63 / 125) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry72C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry72C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (62 / 125) (993 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (425750953 / 1000000000) (592973653 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63240859 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry72C_hz12 hx hc).2
  have hrp := (lowGeometry72C_hz16 hx hc).2
  have hbn := (lowGeometry72C_hz21 hx hc).2
  have hlo := (lowGeometry72C_hz40 hx hc).1
  have hhi := (lowGeometry72C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry73W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (993 / 2000) (497 / 1000) θ := hc

theorem lowGeometry73W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry73W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (503 / 1000) (1007 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry73W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (499479 / 2000000) (500479 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry73W_hz0 hx hc) (lowGeometry73W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (500479 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry73W_hz3 hx hc) (lowGeometry73W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (2796423497076221 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry73W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (8389270491228663 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry73W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (993 / 1000) (497 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry73W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry73W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry73W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (497 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry73W_hz7 hx hc) (lowGeometry73W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (14601770491228663 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry73W_hz6 hx hc) (lowGeometry73W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (14601770491228663 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry73W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry73W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (993 / 50) (497 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry73W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (497 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry73W_hz13 hx hc) (lowGeometry73W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (14912395491228663 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry73W_hz12 hx hc) (lowGeometry73W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (14912395491228663 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry73W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry73W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (497 / 8000000) (θ * x) := bmul (lowGeometry73W_hz0 hx hc) (lowGeometry73W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (30877236580517 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry73W_hz17 hx hc) (lowGeometry73W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (5556728946108223 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry73W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (16670186838324669 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry73W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (16670186838324669 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry73W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry73W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (993 / 250) (497 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry73W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry73W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (22226515696347911 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry73W_hz22 hx hc) (lowGeometry73W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry73W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry73W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry73W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry73W_hz26 hx hc) (lowGeometry73W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry73W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (46728573271607601 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry73W_hz24 hx hc) (lowGeometry73W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (266670186838324669 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry73W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (1137807816774191801 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry73W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (503 / 1000) (143221558936451393 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry73W_hz2 hx hc) (lowGeometry73W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (503 / 1000) (619614809017413173 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry73W_hz33 hx hc) (lowGeometry73W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (503 / 1000) (619614809017413173 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry73W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry73W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (233329813161675331 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry73W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (108885603420124637 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry73W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (438155668162581539 / 1000000000000000000) (1007 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry73W_hz2 hx hc) (lowGeometry73W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (195713547445486969 / 500000000000000000) (1007 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry73W_hz38 hx hc) (lowGeometry73W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (195713547445486969 / 500000000000000000) (1007 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry73W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry73W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (993 / 2000) (497 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (69941461 / 200000000) (350783937 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (29203541 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry73W_hz12 hx hc).2
  have hrp := (lowGeometry73W_hz16 hx hc).2
  have hbn := (lowGeometry73W_hz21 hx hc).2
  have hlo := (lowGeometry73W_hz40 hx hc).1
  have hhi := (lowGeometry73W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry73C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (993 / 2000) (497 / 1000) θ := hc

theorem lowGeometry73C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry73C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (503 / 1000) (1007 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry73C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (499479 / 2000000) (500479 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry73C_hz0 hx hc) (lowGeometry73C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (500479 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry73C_hz3 hx hc) (lowGeometry73C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (2796423497076221 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry73C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (16107399343159033 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry73C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (993 / 1000) (497 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry73C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry73C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry73C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (31057529602336373 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry73C_hz7 hx hc) (lowGeometry73C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (63272328288654439 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry73C_hz6 hx hc) (lowGeometry73C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (63272328288654439 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry73C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry73C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (775533 / 100000) (388157 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry73C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (388157 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry73C_hz13 hx hc) (lowGeometry73C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (64242720788654439 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry73C_hz12 hx hc) (lowGeometry73C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (64242720788654439 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry73C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry73C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (497 / 8000000) (θ * x) := bmul (lowGeometry73C_hz0 hx hc) (lowGeometry73C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (30877236580517 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry73C_hz17 hx hc) (lowGeometry73C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (5556728946108223 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry73C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (6401351745916673 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry73C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (6401351745916673 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry73C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry73C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (324711 / 200000) (162519 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry73C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry73C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (18170176581764417 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry73C_hz22 hx hc) (lowGeometry73C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry73C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry73C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry73C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry73C_hz26 hx hc) (lowGeometry73C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry73C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 0 (18746502360838183 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry73C_hz24 hx hc) (lowGeometry73C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (206401351745916673 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry73C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B 1 (1065037950063540491 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry73C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (503 / 1000) (268123303928496319 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry73C_hz2 hx hc) (lowGeometry73C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (503 / 1000) (554993110217830821 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry73C_hz33 hx hc) (lowGeometry73C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (503 / 1000) (554993110217830821 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry73C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry73C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (193598648254083327 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry73C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (93701091514520703 / 100000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry73C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (14728640322438723 / 31250000000000000) (1007 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry73C_hz2 hx hc) (lowGeometry73C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (452569987957200953 / 1000000000000000000) (1007 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry73C_hz38 hx hc) (lowGeometry73C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry73C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (993 / 2000) (497 / 1000) θ) : B (452569987957200953 / 1000000000000000000) (1007 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry73C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry73C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (993 / 2000) (497 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (106312681 / 250000000) (592480747 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63272329 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry73C_hz12 hx hc).2
  have hrp := (lowGeometry73C_hz16 hx hc).2
  have hbn := (lowGeometry73C_hz21 hx hc).2
  have hlo := (lowGeometry73C_hz40 hx hc).1
  have hhi := (lowGeometry73C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry74W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (497 / 1000) (199 / 400) θ := hc

theorem lowGeometry74W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry74W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (201 / 400) (503 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry74W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (99897 / 400000) (100097 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry74W_hz0 hx hc) (lowGeometry74W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (100097 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry74W_hz3 hx hc) (lowGeometry74W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (1398220129754253 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry74W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (4194660389262759 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry74W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (497 / 500) (199 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry74W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry74W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry74W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (199 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry74W_hz7 hx hc) (lowGeometry74W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (7304035389262759 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry74W_hz6 hx hc) (lowGeometry74W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (7304035389262759 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry74W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry74W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (497 / 25) (199 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry74W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (199 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry74W_hz13 hx hc) (lowGeometry74W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (7459504139262759 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry74W_hz12 hx hc) (lowGeometry74W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (7459504139262759 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry74W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry74W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (199 / 3200000) (θ * x) := bmul (lowGeometry74W_hz0 hx hc) (lowGeometry74W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (123756218905473 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry74W_hz17 hx hc) (lowGeometry74W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (5562288623073083 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry74W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (16686865869219249 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry74W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (16686865869219249 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry74W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry74W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (497 / 125) (199 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry74W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry74W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (22248876376122909 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry74W_hz22 hx hc) (lowGeometry74W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry74W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry74W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry74W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry74W_hz26 hx hc) (lowGeometry74W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry74W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (23387791954350887 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry74W_hz24 hx hc) (lowGeometry74W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (266686865869219249 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry74W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (1137950150834351021 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry74W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (201 / 400) (143097231467419641 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry74W_hz2 hx hc) (lowGeometry74W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (201 / 400) (309582254889190169 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry74W_hz33 hx hc) (lowGeometry74W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (201 / 400) (309582254889190169 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry74W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry74W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (233313134130780751 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry74W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (217740074231710759 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry74W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (3501260393645909 / 8000000000000000) (503 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry74W_hz2 hx hc) (lowGeometry74W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (390881965297036851 / 1000000000000000000) (503 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry74W_hz38 hx hc) (lowGeometry74W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (390881965297036851 / 1000000000000000000) (503 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry74W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry74W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (497 / 1000) (199 / 400) θ) :
    OverlapGuard n θ lowWideWindow (349203773 / 1000000000) (701098027 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (116864567 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry74W_hz12 hx hc).2
  have hrp := (lowGeometry74W_hz16 hx hc).2
  have hbn := (lowGeometry74W_hz21 hx hc).2
  have hlo := (lowGeometry74W_hz40 hx hc).1
  have hhi := (lowGeometry74W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry74C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (497 / 1000) (199 / 400) θ := hc

theorem lowGeometry74C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry74C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (201 / 400) (503 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry74C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (99897 / 400000) (100097 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry74C_hz0 hx hc) (lowGeometry74C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (100097 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry74C_hz3 hx hc) (lowGeometry74C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (1398220129754253 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry74C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (3221499178953799 / 100000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry74C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (497 / 500) (199 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry74C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry74C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry74C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (31088774601936309 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry74C_hz7 hx hc) (lowGeometry74C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (63303766391474299 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry74C_hz6 hx hc) (lowGeometry74C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (63303766391474299 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry74C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry74C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (388157 / 50000) (155419 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry74C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (155419 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry74C_hz13 hx hc) (lowGeometry74C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (64275135141474299 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry74C_hz12 hx hc) (lowGeometry74C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (64275135141474299 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry74C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry74C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (199 / 3200000) (θ * x) := bmul (lowGeometry74C_hz0 hx hc) (lowGeometry74C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (123756218905473 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry74C_hz17 hx hc) (lowGeometry74C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (5562288623073083 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry74C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (32038782468900959 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry74C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (32038782468900959 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry74C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry74C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (162519 / 100000) (65073 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry74C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry74C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (9094228218740239 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry74C_hz22 hx hc) (lowGeometry74C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry74C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry74C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry74C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry74C_hz26 hx hc) (lowGeometry74C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry74C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 0 (9382681010580479 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry74C_hz24 hx hc) (lowGeometry74C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (1032038782468900959 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry74C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B 1 (532552024259945737 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry74C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (201 / 400) (133936834101376353 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry74C_hz2 hx hc) (lowGeometry74C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (201 / 400) (55451269842666637 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry74C_hz33 hx hc) (lowGeometry74C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (201 / 400) (55451269842666637 / 100000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry74C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry74C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (967961217531099041 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry74C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (936948918644287637 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry74C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (470816831618754537 / 1000000000000000000) (503 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry74C_hz2 hx hc) (lowGeometry74C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (452051469597593579 / 1000000000000000000) (503 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry74C_hz38 hx hc) (lowGeometry74C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry74C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (497 / 1000) (199 / 400) θ) : B (452051469597593579 / 1000000000000000000) (503 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry74C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry74C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (497 / 1000) (199 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (424750569 / 1000000000) (591987753 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63303767 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry74C_hz12 hx hc).2
  have hrp := (lowGeometry74C_hz16 hx hc).2
  have hbn := (lowGeometry74C_hz21 hx hc).2
  have hlo := (lowGeometry74C_hz40 hx hc).1
  have hhi := (lowGeometry74C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry75W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (199 / 400) (249 / 500) θ := hc

theorem lowGeometry75W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry75W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (251 / 500) (201 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry75W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (49949 / 200000) (50049 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry75W_hz0 hx hc) (lowGeometry75W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (50049 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry75W_hz3 hx hc) (lowGeometry75W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (699113557031331 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry75W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (2097340671093993 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry75W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (199 / 200) (249 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry75W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry75W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry75W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (249 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry75W_hz7 hx hc) (lowGeometry75W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (3653590671093993 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry75W_hz6 hx hc) (lowGeometry75W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (3653590671093993 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry75W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry75W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (199 / 10) (498 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry75W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (249 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry75W_hz13 hx hc) (lowGeometry75W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (3731403171093993 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry75W_hz12 hx hc) (lowGeometry75W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (3731403171093993 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry75W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry75W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (249 / 4000000) (θ * x) := bmul (lowGeometry75W_hz0 hx hc) (lowGeometry75W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (62001992031873 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry75W_hz17 hx hc) (lowGeometry75W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (5567853806983127 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry75W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (16703561420949381 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry75W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (16703561420949381 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry75W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry75W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (199 / 50) (498 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry75W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry75W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (44542474111795813 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry75W_hz22 hx hc) (lowGeometry75W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry75W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry75W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry75W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry75W_hz26 hx hc) (lowGeometry75W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry75W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (23411297272897973 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry75W_hz24 hx hc) (lowGeometry75W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (266703561420949381 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry75W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (227618526958777981 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry75W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (251 / 500) (285945774491964839 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry75W_hz2 hx hc) (lowGeometry75W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (251 / 500) (77339267941215703 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry75W_hz33 hx hc) (lowGeometry75W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (251 / 500) (77339267941215703 / 125000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry75W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry75W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (233296438579050619 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry75W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (27213614126834369 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry75W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (437159497333467303 / 1000000000000000000) (201 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry75W_hz2 hx hc) (lowGeometry75W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (390336902787671357 / 1000000000000000000) (201 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry75W_hz38 hx hc) (lowGeometry75W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (390336902787671357 / 1000000000000000000) (201 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry75W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry75W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (199 / 400) (249 / 500) θ) :
    OverlapGuard n θ lowWideWindow (348700369 / 1000000000) (700627997 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (58457451 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry75W_hz12 hx hc).2
  have hrp := (lowGeometry75W_hz16 hx hc).2
  have hbn := (lowGeometry75W_hz21 hx hc).2
  have hlo := (lowGeometry75W_hz40 hx hc).1
  have hhi := (lowGeometry75W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry75C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (199 / 400) (249 / 500) θ := hc

theorem lowGeometry75C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry75C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (251 / 500) (201 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry75C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (49949 / 200000) (50049 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry75C_hz0 hx hc) (lowGeometry75C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (50049 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry75C_hz3 hx hc) (lowGeometry75C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (699113557031331 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry75C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (32215152708003733 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry75C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (199 / 200) (249 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry75C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry75C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry75C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (6224003920307249 / 200000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry75C_hz7 hx hc) (lowGeometry75C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (31667586154769989 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry75C_hz6 hx hc) (lowGeometry75C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (31667586154769989 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry75C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry75C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (155419 / 20000) (194469 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry75C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (194469 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry75C_hz13 hx hc) (lowGeometry75C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (32153758654769989 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry75C_hz12 hx hc) (lowGeometry75C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (32153758654769989 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry75C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry75C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (249 / 4000000) (θ * x) := bmul (lowGeometry75C_hz0 hx hc) (lowGeometry75C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (62001992031873 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry75C_hz17 hx hc) (lowGeometry75C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (5567853806983127 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry75C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (8017709482055703 / 250000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry75C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (8017709482055703 / 250000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry75C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry75C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (65073 / 40000) (81423 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry75C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry75C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (18206736293196539 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry75C_hz22 hx hc) (lowGeometry75C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry75C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry75C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry75C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry75C_hz26 hx hc) (lowGeometry75C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry75C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 0 (18784221681483733 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry75C_hz24 hx hc) (lowGeometry75C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (258017709482055703 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry75C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B 1 (1065170214501863959 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry75C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (251 / 500) (6690600409839833 / 12500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry75C_hz2 hx hc) (lowGeometry75C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (251 / 500) (554032254468670373 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry75C_hz33 hx hc) (lowGeometry75C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (251 / 500) (554032254468670373 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry75C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry75C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (241982290517944297 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry75C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (93688686278897271 / 100000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry75C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (4703172051200643 / 10000000000000000) (201 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry75C_hz2 hx hc) (lowGeometry75C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (451532983438580567 / 1000000000000000000) (201 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry75C_hz38 hx hc) (lowGeometry75C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry75C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (199 / 400) (249 / 500) θ) : B (451532983438580567 / 1000000000000000000) (201 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry75C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry75C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (199 / 400) (249 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (424250487 / 1000000000) (36968417 / 62500000) ∧ radiusMinus n θ lowCoreWindow ≤ (63335173 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry75C_hz12 hx hc).2
  have hrp := (lowGeometry75C_hz16 hx hc).2
  have hbn := (lowGeometry75C_hz21 hx hc).2
  have hlo := (lowGeometry75C_hz40 hx hc).1
  have hhi := (lowGeometry75C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry76W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (249 / 500) (997 / 2000) θ := hc

theorem lowGeometry76W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry76W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (1003 / 2000) (251 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry76W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (249747 / 1000000) (250247 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry76W_hz0 hx hc) (lowGeometry76W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (250247 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry76W_hz3 hx hc) (lowGeometry76W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (5592930805937081 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry76W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (16778792417811243 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry76W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (249 / 250) (997 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry76W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry76W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry76W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (997 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry76W_hz7 hx hc) (lowGeometry76W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (29241292417811243 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry76W_hz6 hx hc) (lowGeometry76W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (29241292417811243 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry76W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry76W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (498 / 25) (997 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry76W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (997 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry76W_hz13 hx hc) (lowGeometry76W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (29864417417811243 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry76W_hz12 hx hc) (lowGeometry76W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (29864417417811243 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry76W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry76W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (997 / 16000000) (θ * x) := bmul (lowGeometry76W_hz0 hx hc) (lowGeometry76W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (12425224327019 / 100000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry76W_hz17 hx hc) (lowGeometry76W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (11146849028769969 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry76W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (33440547086309907 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry76W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (33440547086309907 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry76W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry76W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (498 / 125) (997 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry76W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry76W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (44587195471345809 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry76W_hz22 hx hc) (lowGeometry76W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry76W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry76W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry76W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry76W_hz26 hx hc) (lowGeometry76W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry76W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (46869605182890119 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry76W_hz24 hx hc) (lowGeometry76W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (533440547086309907 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry76W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (1138235269102966469 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry76W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (1003 / 2000) (35712131568105573 / 62500000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry76W_hz2 hx hc) (lowGeometry76W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (1003 / 2000) (618263710272579287 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry76W_hz33 hx hc) (lowGeometry76W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (1003 / 2000) (618263710272579287 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry76W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry76W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (466559452913690093 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry76W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (217677723103121803 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry76W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (3411418066756737 / 7812500000000000) (251 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry76W_hz2 hx hc) (lowGeometry76W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (389791907361972217 / 1000000000000000000) (251 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry76W_hz38 hx hc) (lowGeometry76W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (389791907361972217 / 1000000000000000000) (251 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry76W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry76W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (249 / 500) (997 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (348197093 / 1000000000) (140031557 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (11696517 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry76W_hz12 hx hc).2
  have hrp := (lowGeometry76W_hz16 hx hc).2
  have hbn := (lowGeometry76W_hz21 hx hc).2
  have hlo := (lowGeometry76W_hz40 hx hc).1
  have hhi := (lowGeometry76W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry76C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (249 / 500) (997 / 2000) θ := hc

theorem lowGeometry76C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry76C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (1003 / 2000) (251 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry76C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (249747 / 1000000) (250247 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry76C_hz0 hx hc) (lowGeometry76C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (250247 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry76C_hz3 hx hc) (lowGeometry76C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (5592930805937081 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry76C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (32215281442197587 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry76C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (249 / 250) (997 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry76C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry76C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry76C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (31151264601136181 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry76C_hz7 hx hc) (lowGeometry76C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (7920818255416721 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry76C_hz6 hx hc) (lowGeometry76C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (7920818255416721 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry76C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry76C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (194469 / 25000) (778657 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry76C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (778657 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry76C_hz13 hx hc) (lowGeometry76C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (8042483411666721 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry76C_hz12 hx hc) (lowGeometry76C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (8042483411666721 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry76C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry76C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (997 / 16000000) (θ * x) := bmul (lowGeometry76C_hz0 hx hc) (lowGeometry76C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (12425224327019 / 100000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry76C_hz17 hx hc) (lowGeometry76C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (11146849028769969 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry76C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (32102925202857511 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry76C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (32102925202857511 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry76C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry76C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (81423 / 50000) (326019 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry76C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry76C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (91125080744563 / 5000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry76C_hz22 hx hc) (lowGeometry76C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry76C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry76C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry76C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry76C_hz26 hx hc) (lowGeometry76C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry76C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 0 (4700770335451627 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry76C_hz24 hx hc) (lowGeometry76C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (1032102925202857511 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry76C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B 1 (532618224106147643 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry76C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (1003 / 2000) (267374348501286117 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry76C_hz2 hx hc) (lowGeometry76C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (1003 / 2000) (276775889172189371 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry76C_hz33 hx hc) (lowGeometry76C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (1003 / 2000) (276775889172189371 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry76C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry76C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (967897074797142489 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry76C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (936824747400865241 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry76C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (234908805410766959 / 500000000000000000) (251 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry76C_hz2 hx hc) (lowGeometry76C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (45101452947972741 / 100000000000000000) (251 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry76C_hz38 hx hc) (lowGeometry76C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry76C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (249 / 500) (997 / 2000) θ) : B (45101452947972741 / 100000000000000000) (251 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry76C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry76C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (249 / 500) (997 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (423750479 / 1000000000) (591001503 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63366547 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry76C_hz12 hx hc).2
  have hrp := (lowGeometry76C_hz16 hx hc).2
  have hbn := (lowGeometry76C_hz21 hx hc).2
  have hlo := (lowGeometry76C_hz40 hx hc).1
  have hhi := (lowGeometry76C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry77W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (997 / 2000) (499 / 1000) θ := hc

theorem lowGeometry77W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry77W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (501 / 1000) (1003 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry77W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (499497 / 2000000) (500497 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry77W_hz0 hx hc) (lowGeometry77W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (500497 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry77W_hz3 hx hc) (lowGeometry77W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (87389805752239 / 15625000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry77W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (262169417256717 / 3906250000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry77W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (997 / 1000) (499 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry77W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry77W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry77W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (499 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry77W_hz7 hx hc) (lowGeometry77W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (457091292256717 / 3906250000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry77W_hz6 hx hc) (lowGeometry77W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (457091292256717 / 3906250000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry77W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry77W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (997 / 50) (499 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry77W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (499 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry77W_hz13 hx hc) (lowGeometry77W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (466837386006717 / 3906250000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry77W_hz12 hx hc) (lowGeometry77W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (466837386006717 / 3906250000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry77W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry77W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (499 / 8000000) (θ * x) := bmul (lowGeometry77W_hz0 hx hc) (lowGeometry77W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (124500998003993 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry77W_hz17 hx hc) (lowGeometry77W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (11158001523749359 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry77W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (33474004571248077 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry77W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (33474004571248077 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry77W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry77W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (997 / 250) (499 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry77W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry77W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (8926383366179161 / 200000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry77W_hz22 hx hc) (lowGeometry77W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry77W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry77W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry77W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry77W_hz26 hx hc) (lowGeometry77W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry77W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (11729153954996073 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry77W_hz24 hx hc) (lowGeometry77W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (533474004571248077 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry77W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (1138378054213136057 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry77W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (501 / 1000) (570896594187887733 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry77W_hz2 hx hc) (lowGeometry77W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (501 / 1000) (24712528400314881 / 40000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry77W_hz33 hx hc) (lowGeometry77W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (501 / 1000) (24712528400314881 / 40000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry77W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry77W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (466525995428751923 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry77W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (10882325220539393 / 12500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry77W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (436163594839218871 / 1000000000000000000) (1003 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry77W_hz2 hx hc) (lowGeometry77W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (389246979019234579 / 1000000000000000000) (1003 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry77W_hz38 hx hc) (lowGeometry77W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (389246979019234579 / 1000000000000000000) (1003 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry77W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry77W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (997 / 2000) (499 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (173846973 / 500000000) (69968739 / 100000000) ∧ radiusMinus n θ lowWideWindow ≤ (117015371 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry77W_hz12 hx hc).2
  have hrp := (lowGeometry77W_hz16 hx hc).2
  have hbn := (lowGeometry77W_hz21 hx hc).2
  have hlo := (lowGeometry77W_hz40 hx hc).1
  have hhi := (lowGeometry77W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry77C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (997 / 2000) (499 / 1000) θ := hc

theorem lowGeometry77C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry77C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (501 / 1000) (1003 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry77C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (499497 / 2000000) (500497 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry77C_hz0 hx hc) (lowGeometry77C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (500497 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry77C_hz3 hx hc) (lowGeometry77C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (87389805752239 / 15625000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry77C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (6443075598501077 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry77C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (997 / 1000) (499 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry77C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry77C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry77C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (31182509600736117 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry77C_hz7 hx hc) (lowGeometry77C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (31698943796620751 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry77C_hz6 hx hc) (lowGeometry77C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (31698943796620751 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry77C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry77C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (778657 / 100000) (389719 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry77C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (389719 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry77C_hz13 hx hc) (lowGeometry77C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (32186092546620751 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry77C_hz12 hx hc) (lowGeometry77C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (32186092546620751 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry77C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry77C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (499 / 8000000) (θ * x) := bmul (lowGeometry77C_hz0 hx hc) (lowGeometry77C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (124500998003993 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry77C_hz17 hx hc) (lowGeometry77C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (11158001523749359 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry77C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (16067522194199077 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry77C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (16067522194199077 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry77C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry77C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (326019 / 200000) (163173 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry77C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry77C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (18243296004628661 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry77C_hz22 hx hc) (lowGeometry77C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry77C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry77C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry77C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry77C_hz26 hx hc) (lowGeometry77C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry77C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 0 (18821941002129283 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry77C_hz24 hx hc) (lowGeometry77C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (516067522194199077 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry77C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B 1 (266325687463660157 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry77C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (501 / 1000) (21369973162084091 / 40000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry77C_hz2 hx hc) (lowGeometry77C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (501 / 1000) (276535635027115779 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry77C_hz33 hx hc) (lowGeometry77C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (501 / 1000) (276535635027115779 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry77C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry77C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (483932477805800923 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry77C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (936762572301048011 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry77C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (469318048722825053 / 1000000000000000000) (1003 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry77C_hz2 hx hc) (lowGeometry77C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (45049610772069577 / 100000000000000000) (1003 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry77C_hz38 hx hc) (lowGeometry77C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry77C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (997 / 2000) (499 / 1000) θ) : B (45049610772069577 / 100000000000000000) (1003 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry77C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry77C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (997 / 2000) (499 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (84650109 / 200000000) (295254123 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (123824 / 1953125) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry77C_hz12 hx hc).2
  have hrp := (lowGeometry77C_hz16 hx hc).2
  have hbn := (lowGeometry77C_hz21 hx hc).2
  have hlo := (lowGeometry77C_hz40 hx hc).1
  have hhi := (lowGeometry77C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry78W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (499 / 1000) (999 / 2000) θ := hc

theorem lowGeometry78W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry78W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (1001 / 2000) (501 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry78W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (499499 / 2000000) (500499 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry78W_hz0 hx hc) (lowGeometry78W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (500499 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry78W_hz3 hx hc) (lowGeometry78W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (559295874291953 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry78W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (1677887622875859 / 25000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry78W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (499 / 500) (999 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry78W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry78W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry78W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (999 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry78W_hz7 hx hc) (lowGeometry78W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (2926637622875859 / 25000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry78W_hz6 hx hc) (lowGeometry78W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (2926637622875859 / 25000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry78W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry78W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (499 / 25) (999 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry78W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (999 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry78W_hz13 hx hc) (lowGeometry78W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (2989075122875859 / 25000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry78W_hz12 hx hc) (lowGeometry78W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (2989075122875859 / 25000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry78W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry78W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (999 / 16000000) (θ * x) := bmul (lowGeometry78W_hz0 hx hc) (lowGeometry78W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (499000999001 / 4000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry78W_hz17 hx hc) (lowGeometry78W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (11169165132195423 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry78W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (33507495396586269 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry78W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (33507495396586269 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry78W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry78W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (499 / 125) (999 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry78W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry78W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (44676638190445801 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry78W_hz22 hx hc) (lowGeometry78W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry78W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry78W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry78W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry78W_hz26 hx hc) (lowGeometry78W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry78W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (9392725291415693 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry78W_hz24 hx hc) (lowGeometry78W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (533507495396586269 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry78W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (1138520990577354077 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry78W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (1001 / 2000) (570399016279254393 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry78W_hz2 hx hc) (lowGeometry78W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (1001 / 2000) (308681321368166429 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry78W_hz33 hx hc) (lowGeometry78W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (1001 / 2000) (308681321368166429 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry78W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry78W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (466492504603413731 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry78W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (217615256851165981 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry78W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (435665744216034293 / 1000000000000000000) (501 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry78W_hz2 hx hc) (lowGeometry78W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (97175529439738957 / 250000000000000000) (501 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry78W_hz38 hx hc) (lowGeometry78W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (97175529439738957 / 250000000000000000) (501 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry78W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry78W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (499 / 1000) (999 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (347190927 / 1000000000) (174804203 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (23413101 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry78W_hz12 hx hc).2
  have hrp := (lowGeometry78W_hz16 hx hc).2
  have hbn := (lowGeometry78W_hz21 hx hc).2
  have hlo := (lowGeometry78W_hz40 hx hc).1
  have hhi := (lowGeometry78W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry78C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (499 / 1000) (999 / 2000) θ := hc

theorem lowGeometry78C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry78C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (1001 / 2000) (501 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry78C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (499499 / 2000000) (500499 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry78C_hz0 hx hc) (lowGeometry78C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (500499 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry78C_hz3 hx hc) (lowGeometry78C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (559295874291953 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry78C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (32215442359216493 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry78C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (499 / 500) (999 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry78C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry78C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry78C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (31213754600336053 / 1000000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry78C_hz7 hx hc) (lowGeometry78C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (31714598479776273 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry78C_hz6 hx hc) (lowGeometry78C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (31714598479776273 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry78C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry78C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (389719 / 50000) (780219 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry78C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (780219 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry78C_hz13 hx hc) (lowGeometry78C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (32202235354776273 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry78C_hz12 hx hc) (lowGeometry78C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (32202235354776273 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry78C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry78C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (999 / 16000000) (θ * x) := bmul (lowGeometry78C_hz0 hx hc) (lowGeometry78C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (499000999001 / 4000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry78C_hz17 hx hc) (lowGeometry78C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (11169165132195423 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry78C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (32167195580722819 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry78C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (32167195580722819 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry78C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry78C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (163173 / 100000) (326673 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry78C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry78C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (18261575860344721 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry78C_hz22 hx hc) (lowGeometry78C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry78C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry78C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry78C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry78C_hz26 hx hc) (lowGeometry78C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry78C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 0 (18840800662452057 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry78C_hz24 hx hc) (lowGeometry78C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (1032167195580722819 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry78C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B 1 (33292784988530441 / 31250000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry78C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (1001 / 2000) (533749928936120031 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry78C_hz2 hx hc) (lowGeometry78C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (1001 / 2000) (69073841199821511 / 125000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry78C_hz33 hx hc) (lowGeometry78C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (1001 / 2000) (69073841199821511 / 125000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry78C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry78C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (967832804419277181 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry78C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (187340067462016567 / 200000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry78C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (234409259411848229 / 500000000000000000) (501 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry78C_hz2 hx hc) (lowGeometry78C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (449977718161244401 / 1000000000000000000) (501 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry78C_hz38 hx hc) (lowGeometry78C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry78C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (499 / 1000) (999 / 2000) θ) : B (449977718161244401 / 1000000000000000000) (501 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry78C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry78C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (499 / 1000) (999 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (105687671 / 250000000) (590014901 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63429197 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry78C_hz12 hx hc).2
  have hrp := (lowGeometry78C_hz16 hx hc).2
  have hbn := (lowGeometry78C_hz21 hx hc).2
  have hlo := (lowGeometry78C_hz40 hx hc).1
  have hhi := (lowGeometry78C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry79W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (999 / 2000) (1 / 2) θ := hc

theorem lowGeometry79W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry79W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (1 / 2) (1001 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry79W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (999 / 4000) (1001 / 4000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry79W_hz0 hx hc) (lowGeometry79W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1001 / 32000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry79W_hz3 hx hc) (lowGeometry79W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (2796482165149637 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry79W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (8389446495448911 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry79W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (999 / 1000) 1 ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry79W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry79W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry79W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 20) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry79W_hz7 hx hc) (lowGeometry79W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (14639446495448911 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry79W_hz6 hx hc) (lowGeometry79W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (14639446495448911 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry79W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry79W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (999 / 50) 20 (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry79W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 400) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry79W_hz13 hx hc) (lowGeometry79W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (14951946495448911 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry79W_hz12 hx hc) (lowGeometry79W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (14951946495448911 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry79W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry79W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 16000) (θ * x) := bmul (lowGeometry79W_hz0 hx hc) (lowGeometry79W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 8000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry79W_hz17 hx hc) (lowGeometry79W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (11180339887498949 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry79W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (33541019662496847 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry79W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (33541019662496847 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry79W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry79W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (999 / 250) 4 (θ * (8 : ℝ)) := bmul (lowGeometry79W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry79W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (11180339887498949 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry79W_hz22 hx hc) (lowGeometry79W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry79W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry79W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry79W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry79W_hz26 hx hc) (lowGeometry79W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry79W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (11752659273543159 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry79W_hz24 hx hc) (lowGeometry79W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (533541019662496847 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry79W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (1138664078649987389 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry79W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (1 / 2) (569901371364318689 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry79W_hz2 hx hc) (lowGeometry79W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (1 / 2) (24676480338339653 / 40000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry79W_hz33 hx hc) (lowGeometry79W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (1 / 2) (24676480338339653 / 40000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry79W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry79W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (466458980337503153 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry79W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (217583980337503153 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry79W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (217583980337503153 / 500000000000000000) (1001 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry79W_hz2 hx hc) (lowGeometry79W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (38815732358083367 / 100000000000000000) (1001 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry79W_hz38 hx hc) (lowGeometry79W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (38815732358083367 / 100000000000000000) (1001 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry79W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry79W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (999 / 2000) (1 / 2) θ) :
    OverlapGuard n θ lowWideWindow (69337607 / 200000000) (174686513 / 250000000) ∧ radiusMinus n θ lowWideWindow ≤ (29278893 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry79W_hz12 hx hc).2
  have hrp := (lowGeometry79W_hz16 hx hc).2
  have hbn := (lowGeometry79W_hz21 hx hc).2
  have hlo := (lowGeometry79W_hz40 hx hc).1
  have hhi := (lowGeometry79W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry79C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (999 / 2000) (1 / 2) θ := hc

theorem lowGeometry79C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry79C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (1 / 2) (1001 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry79C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (999 / 4000) (1001 / 4000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry79C_hz0 hx hc) (lowGeometry79C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1001 / 32000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry79C_hz3 hx hc) (lowGeometry79C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (2796482165149637 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry79C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (32215474542523819 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry79C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (999 / 1000) 1 ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry79C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry79C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry79C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (7811249899983997 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry79C_hz7 hx hc) (lowGeometry79C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (63460474142459807 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry79C_hz6 hx hc) (lowGeometry79C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (63460474142459807 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry79C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry79C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (780219 / 100000) (781 / 100) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry79C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (781 / 800000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry79C_hz13 hx hc) (lowGeometry79C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (64436724142459807 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry79C_hz12 hx hc) (lowGeometry79C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (64436724142459807 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry79C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry79C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 16000) (θ * x) := bmul (lowGeometry79C_hz0 hx hc) (lowGeometry79C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1 / 8000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry79C_hz17 hx hc) (lowGeometry79C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (11180339887498949 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry79C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (16099689437998487 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry79C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (16099689437998487 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry79C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry79C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (326673 / 200000) (327 / 200) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry79C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry79C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (9139927858030391 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry79C_hz22 hx hc) (lowGeometry79C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry79C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry79C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry79C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry79C_hz26 hx hc) (lowGeometry79C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry79C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 0 (1178728770173427 / 62500000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry79C_hz24 hx hc) (lowGeometry79C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (516099689437998487 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry79C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B 1 (1065435557751993949 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry79C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (1 / 2) (133312624163718243 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry79C_hz2 hx hc) (lowGeometry79C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (1 / 2) (138027539244411951 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry79C_hz33 hx hc) (lowGeometry79C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (1 / 2) (138027539244411951 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry79C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry79C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (483900310562001513 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry79C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (234159510562001513 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry79C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (234159510562001513 / 500000000000000000) (1001 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry79C_hz2 hx hc) (lowGeometry79C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (224729680400614097 / 500000000000000000) (1001 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry79C_hz38 hx hc) (lowGeometry79C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry79C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (999 / 2000) (1 / 2) θ) : B (224729680400614097 / 500000000000000000) (1001 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry79C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry79C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (999 / 2000) (1 / 2) θ) :
    OverlapGuard n θ lowCoreWindow (26390681 / 62500000) (589521469 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (2538419 / 40000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry79C_hz12 hx hc).2
  have hrp := (lowGeometry79C_hz16 hx hc).2
  have hbn := (lowGeometry79C_hz21 hx hc).2
  have hlo := (lowGeometry79C_hz40 hx hc).1
  have hhi := (lowGeometry79C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry80W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (1 / 2) (1001 / 2000) θ := hc

theorem lowGeometry80W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry80W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 2000) (1 / 2) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 4000) (1001 / 4000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry80W_hz0 hx hc) (lowGeometry80W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1001 / 32000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry80W_hz3 hx hc) (lowGeometry80W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (2796482165149637 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry80W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (8389446495448911 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry80W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (1001 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry80W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry80W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry80W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1001 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry80W_hz7 hx hc) (lowGeometry80W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (14645696495448911 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry80W_hz6 hx hc) (lowGeometry80W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (14645696495448911 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry80W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry80W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 20 (1001 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry80W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1001 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry80W_hz13 hx hc) (lowGeometry80W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (14958508995448911 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry80W_hz12 hx hc) (lowGeometry80W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (14958508995448911 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry80W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry80W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1001 / 16000000) (θ * x) := bmul (lowGeometry80W_hz0 hx hc) (lowGeometry80W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (125250250250251 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry80W_hz17 hx hc) (lowGeometry80W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1398940727893849 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry80W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (4196822183681547 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry80W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (4196822183681547 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry80W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry80W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 4 (1001 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry80W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry80W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (699470014211653 / 15625000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry80W_hz22 hx hc) (lowGeometry80W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry80W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry80W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry80W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry80W_hz26 hx hc) (lowGeometry80W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry80W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (47057647731266809 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry80W_hz24 hx hc) (lowGeometry80W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (66696822183681547 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry80W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (1138807318886818541 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry80W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 2000) (569403659443409271 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry80W_hz2 hx hc) (lowGeometry80W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 2000) (7705766339683451 / 12500000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry80W_hz33 hx hc) (lowGeometry80W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 2000) (7705766339683451 / 12500000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry80W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry80W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (58303177816318453 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry80W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (217552674782799883 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry80W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (217335122108017083 / 500000000000000000) (1 / 2) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry80W_hz2 hx hc) (lowGeometry80W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (387612596484767357 / 1000000000000000000) (1 / 2) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry80W_hz38 hx hc) (lowGeometry80W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (387612596484767357 / 1000000000000000000) (1 / 2) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry80W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry80W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1 / 2) (1001 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (43273159 / 125000000) (69827511 / 100000000) ∧ radiusMinus n θ lowWideWindow ≤ (29291393 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry80W_hz12 hx hc).2
  have hrp := (lowGeometry80W_hz16 hx hc).2
  have hbn := (lowGeometry80W_hz21 hx hc).2
  have hlo := (lowGeometry80W_hz40 hx hc).1
  have hhi := (lowGeometry80W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry80C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (1 / 2) (1001 / 2000) θ := hc

theorem lowGeometry80C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry80C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 2000) (1 / 2) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 4000) (1001 / 4000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry80C_hz0 hx hc) (lowGeometry80C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1001 / 32000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry80C_hz3 hx hc) (lowGeometry80C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (2796482165149637 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry80C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (32215474542523819 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry80C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (1001 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry80C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry80C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry80C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (7819061149883981 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry80C_hz7 hx hc) (lowGeometry80C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (63491719142059743 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry80C_hz6 hx hc) (lowGeometry80C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (63491719142059743 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry80C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry80C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (781 / 100) (781781 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry80C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (781781 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry80C_hz13 hx hc) (lowGeometry80C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (64468945392059743 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry80C_hz12 hx hc) (lowGeometry80C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (64468945392059743 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry80C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry80C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1001 / 16000000) (θ * x) := bmul (lowGeometry80C_hz0 hx hc) (lowGeometry80C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (125250250250251 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry80C_hz17 hx hc) (lowGeometry80C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (1398940727893849 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry80C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (32231594370674281 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry80C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (32231594370674281 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry80C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry80C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (327 / 200) (327327 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry80C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry80C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (18298135571776843 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry80C_hz22 hx hc) (lowGeometry80C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry80C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry80C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry80C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry80C_hz26 hx hc) (lowGeometry80C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry80C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 0 (18878519983097607 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry80C_hz24 hx hc) (lowGeometry80C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (1032231594370674281 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry80C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B 1 (213100412883404849 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry80C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 2000) (532751032208512123 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry80C_hz2 hx hc) (lowGeometry80C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 2000) (55162955219160973 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry80C_hz33 hx hc) (lowGeometry80C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (999 / 2000) (55162955219160973 / 100000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry80C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry80C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (967768405629325719 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry80C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (11707196086679089 / 12500000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry80C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (116954888905924099 / 250000000000000000) (1 / 2) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry80C_hz2 hx hc) (lowGeometry80C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (448941035640598789 / 1000000000000000000) (1 / 2) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry80C_hz38 hx hc) (lowGeometry80C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry80C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (1001 / 2000) θ) : B (448941035640598789 / 1000000000000000000) (1 / 2) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry80C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry80C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1 / 2) (1001 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (421751181 / 1000000000) (11780559 / 20000000) ∧ radiusMinus n θ lowCoreWindow ≤ (1587293 / 25000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry80C_hz12 hx hc).2
  have hrp := (lowGeometry80C_hz16 hx hc).2
  have hbn := (lowGeometry80C_hz21 hx hc).2
  have hlo := (lowGeometry80C_hz40 hx hc).1
  have hhi := (lowGeometry80C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry81W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (1001 / 2000) (501 / 1000) θ := hc

theorem lowGeometry81W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry81W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499 / 1000) (999 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry81W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499499 / 2000000) (500499 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry81W_hz0 hx hc) (lowGeometry81W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (500499 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry81W_hz3 hx hc) (lowGeometry81W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (559295874291953 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry81W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (1677887622875859 / 25000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry81W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (1001 / 1000) (501 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry81W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry81W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry81W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (501 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry81W_hz7 hx hc) (lowGeometry81W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (2930387622875859 / 25000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry81W_hz6 hx hc) (lowGeometry81W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (2930387622875859 / 25000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry81W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry81W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (1001 / 50) (501 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry81W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (501 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry81W_hz13 hx hc) (lowGeometry81W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (2993012622875859 / 25000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry81W_hz12 hx hc) (lowGeometry81W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (2993012622875859 / 25000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry81W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry81W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (501 / 8000000) (θ * x) := bmul (lowGeometry81W_hz0 hx hc) (lowGeometry81W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (125501002004009 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry81W_hz17 hx hc) (lowGeometry81W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (5601361486371171 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry81W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (16804084459113513 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry81W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (16804084459113513 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry81W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry81W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (1001 / 250) (501 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry81W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry81W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (11202700567273947 / 250000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry81W_hz22 hx hc) (lowGeometry81W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry81W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry81W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry81W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry81W_hz26 hx hc) (lowGeometry81W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry81W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (23552329184180491 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry81W_hz24 hx hc) (lowGeometry81W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (266804084459113513 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry81W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (1138950711745052429 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry81W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499 / 1000) (568905880516653689 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry81W_hz2 hx hc) (lowGeometry81W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499 / 1000) (616010538885014671 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry81W_hz33 hx hc) (lowGeometry81W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499 / 1000) (616010538885014671 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry81W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry81W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (233195915540886487 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry81W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (43504268019961811 / 50000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry81W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (434172594839218873 / 1000000000000000000) (999 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry81W_hz2 hx hc) (lowGeometry81W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (387067936470857891 / 1000000000000000000) (999 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry81W_hz38 hx hc) (lowGeometry81W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (387067936470857891 / 1000000000000000000) (999 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry81W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry81W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1001 / 2000) (501 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (86420659 / 250000000) (348901993 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (23443101 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry81W_hz12 hx hc).2
  have hrp := (lowGeometry81W_hz16 hx hc).2
  have hbn := (lowGeometry81W_hz21 hx hc).2
  have hlo := (lowGeometry81W_hz40 hx hc).1
  have hhi := (lowGeometry81W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry81C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (1001 / 2000) (501 / 1000) θ := hc

theorem lowGeometry81C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry81C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499 / 1000) (999 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry81C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499499 / 2000000) (500499 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry81C_hz0 hx hc) (lowGeometry81C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (500499 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry81C_hz3 hx hc) (lowGeometry81C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (559295874291953 / 100000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry81C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (32215442359216493 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry81C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (1001 / 1000) (501 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry81C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry81C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry81C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (1565374479956793 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry81C_hz7 hx hc) (lowGeometry81C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (63522931958352353 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry81C_hz6 hx hc) (lowGeometry81C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (63522931958352353 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry81C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry81C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (781781 / 100000) (391281 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry81C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (391281 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry81C_hz13 hx hc) (lowGeometry81C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (64501134458352353 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry81C_hz12 hx hc) (lowGeometry81C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (64501134458352353 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry81C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry81C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (501 / 8000000) (θ * x) := bmul (lowGeometry81C_hz0 hx hc) (lowGeometry81C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (125501002004009 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry81C_hz17 hx hc) (lowGeometry81C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (5601361486371171 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry81C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (6452768432299589 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry81C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (6452768432299589 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry81C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry81C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (327327 / 200000) (163827 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry81C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry81C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (2289551928436613 / 125000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry81C_hz22 hx hc) (lowGeometry81C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry81C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry81C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry81C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry81C_hz26 hx hc) (lowGeometry81C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry81C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 0 (9448689821710191 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry81C_hz24 hx hc) (lowGeometry81C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (206452768432299589 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry81C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B 1 (1065568639834017943 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry81C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499 / 1000) (532251535597091963 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry81C_hz2 hx hc) (lowGeometry81C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499 / 1000) (110229783048102469 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry81C_hz33 hx hc) (lowGeometry81C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (499 / 1000) (110229783048102469 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry81C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry81C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (193547231567700411 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry81C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (468256635594013081 / 500000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry81C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (233660061161412527 / 500000000000000000) (999 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry81C_hz2 hx hc) (lowGeometry81C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (3503302677182849 / 7812500000000000) (999 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry81C_hz38 hx hc) (lowGeometry81C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry81C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1001 / 2000) (501 / 1000) θ) : B (3503302677182849 / 7812500000000000) (999 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry81C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry81C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1001 / 2000) (501 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (21062577 / 50000000) (588534343 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15880733 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry81C_hz12 hx hc).2
  have hrp := (lowGeometry81C_hz16 hx hc).2
  have hbn := (lowGeometry81C_hz21 hx hc).2
  have hlo := (lowGeometry81C_hz40 hx hc).1
  have hhi := (lowGeometry81C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry82W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (501 / 1000) (1003 / 2000) θ := hc

theorem lowGeometry82W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry82W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (997 / 2000) (499 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry82W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (499497 / 2000000) (500497 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry82W_hz0 hx hc) (lowGeometry82W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (500497 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry82W_hz3 hx hc) (lowGeometry82W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (87389805752239 / 15625000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry82W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (262169417256717 / 3906250000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry82W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (501 / 500) (1003 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry82W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry82W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry82W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1003 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry82W_hz7 hx hc) (lowGeometry82W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (458067854756717 / 3906250000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry82W_hz6 hx hc) (lowGeometry82W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (458067854756717 / 3906250000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry82W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry82W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (501 / 25) (1003 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry82W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1003 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry82W_hz13 hx hc) (lowGeometry82W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (467862776631717 / 3906250000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry82W_hz12 hx hc) (lowGeometry82W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (467862776631717 / 3906250000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry82W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry82W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1003 / 16000000) (θ * x) := bmul (lowGeometry82W_hz0 hx hc) (lowGeometry82W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (125752256770311 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry82W_hz17 hx hc) (lowGeometry82W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (2242786273993231 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry82W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (6728358821979693 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry82W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (6728358821979693 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry82W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry82W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (501 / 125) (1003 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry82W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry82W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (5606940453580723 / 125000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry82W_hz22 hx hc) (lowGeometry82W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry82W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry82W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry82W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry82W_hz26 hx hc) (lowGeometry82W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry82W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (9430333801091031 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry82W_hz24 hx hc) (lowGeometry82W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (106728358821979693 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry82W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (1139094257683325057 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry82W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (997 / 2000) (142102008645994801 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry82W_hz2 hx hc) (lowGeometry82W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (997 / 2000) (615559703589434359 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry82W_hz33 hx hc) (lowGeometry82W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (997 / 2000) (615559703589434359 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry82W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry82W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (93271641178020307 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry82W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (108744988100517167 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry82W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (433675012544862461 / 1000000000000000000) (499 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry82W_hz2 hx hc) (lowGeometry82W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (193261671769703653 / 500000000000000000) (499 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry82W_hz38 hx hc) (lowGeometry82W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (193261671769703653 / 500000000000000000) (499 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry82W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry82W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (501 / 1000) (1003 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (10786879 / 31250000) (697332679 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (117265371 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry82W_hz12 hx hc).2
  have hrp := (lowGeometry82W_hz16 hx hc).2
  have hbn := (lowGeometry82W_hz21 hx hc).2
  have hlo := (lowGeometry82W_hz40 hx hc).1
  have hhi := (lowGeometry82W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry82C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (501 / 1000) (1003 / 2000) θ := hc

theorem lowGeometry82C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry82C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (997 / 2000) (499 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry82C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (499497 / 2000000) (500497 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry82C_hz0 hx hc) (lowGeometry82C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (500497 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry82C_hz3 hx hc) (lowGeometry82C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (87389805752239 / 15625000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry82C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (6443075598501077 / 200000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry82C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (501 / 500) (1003 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry82C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry82C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry82C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (7834683649683949 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry82C_hz7 hx hc) (lowGeometry82C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (63554112591241181 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry82C_hz6 hx hc) (lowGeometry82C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (63554112591241181 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry82C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry82C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (391281 / 50000) (783343 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry82C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (783343 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry82C_hz13 hx hc) (lowGeometry82C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (64533291341241181 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry82C_hz12 hx hc) (lowGeometry82C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (64533291341241181 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry82C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry82C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (1003 / 16000000) (θ * x) := bmul (lowGeometry82C_hz0 hx hc) (lowGeometry82C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (125752256770311 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry82C_hz17 hx hc) (lowGeometry82C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (2242786273993231 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry82C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (32296122345502527 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry82C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (32296122345502527 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry82C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry82C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (163827 / 100000) (327981 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry82C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry82C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (4583673820802241 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry82C_hz22 hx hc) (lowGeometry82C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry82C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry82C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry82C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry82C_hz26 hx hc) (lowGeometry82C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry82C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 0 (4729059825935789 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry82C_hz24 hx hc) (lowGeometry82C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (1032296122345502527 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry82C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B 1 (532817642104780361 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry82C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (997 / 2000) (531752006820570801 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry82C_hz2 hx hc) (lowGeometry82C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (997 / 2000) (550668246124313957 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry82C_hz33 hx hc) (lowGeometry82C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (997 / 2000) (550668246124313957 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry82C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry82C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (967703877654497473 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry82C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (936450794827550613 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry82C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (23341036061076699 / 50000000000000000) (499 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry82C_hz2 hx hc) (lowGeometry82C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (55988060239723853 / 125000000000000000) (499 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry82C_hz38 hx hc) (lowGeometry82C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry82C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (501 / 1000) (1003 / 2000) θ) : B (55988060239723853 / 125000000000000000) (499 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry82C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry82C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (501 / 1000) (1003 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (105187993 / 250000000) (73505081 / 125000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63554113 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry82C_hz12 hx hc).2
  have hrp := (lowGeometry82C_hz16 hx hc).2
  have hbn := (lowGeometry82C_hz21 hx hc).2
  have hlo := (lowGeometry82C_hz40 hx hc).1
  have hhi := (lowGeometry82C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry83W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (1003 / 2000) (251 / 500) θ := hc

theorem lowGeometry83W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry83W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249 / 500) (997 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry83W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249747 / 1000000) (250247 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry83W_hz0 hx hc) (lowGeometry83W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (250247 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry83W_hz3 hx hc) (lowGeometry83W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (5592930805937081 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry83W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (16778792417811243 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry83W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (1003 / 1000) (251 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry83W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry83W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry83W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (251 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry83W_hz7 hx hc) (lowGeometry83W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (29328792417811243 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry83W_hz6 hx hc) (lowGeometry83W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (29328792417811243 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry83W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry83W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (1003 / 50) (502 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry83W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (251 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry83W_hz13 hx hc) (lowGeometry83W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (29956292417811243 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry83W_hz12 hx hc) (lowGeometry83W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (29956292417811243 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry83W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry83W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (251 / 4000000) (θ * x) := bmul (lowGeometry83W_hz0 hx hc) (lowGeometry83W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (63002008032129 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry83W_hz17 hx hc) (lowGeometry83W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (2245030209723317 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry83W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (6735090629169951 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry83W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (6735090629169951 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry83W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry83W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (1003 / 250) (502 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry83W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry83W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (2245012249409789 / 50000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry83W_hz22 hx hc) (lowGeometry83W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry83W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry83W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry83W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry83W_hz26 hx hc) (lowGeometry83W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry83W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (2949917477659333 / 62500000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry83W_hz24 hx hc) (lowGeometry83W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (106735090629169951 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry83W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (1139237957161712309 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry83W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249 / 500) (567910121645113587 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry83W_hz2 hx hc) (lowGeometry83W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249 / 500) (123021760257532583 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry83W_hz33 hx hc) (lowGeometry83W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249 / 500) (123021760257532583 / 200000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry83W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry83W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (93264909370830049 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry83W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (217458582998728567 / 250000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry83W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (86635499466693461 / 200000000000000000) (997 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry83W_hz2 hx hc) (lowGeometry83W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (385978817690917977 / 1000000000000000000) (997 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry83W_hz38 hx hc) (lowGeometry83W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (385978817690917977 / 1000000000000000000) (997 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry83W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry83W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1003 / 2000) (251 / 500) θ) :
    OverlapGuard n θ lowWideWindow (86169437 / 250000000) (696861191 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (11731517 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry83W_hz12 hx hc).2
  have hrp := (lowGeometry83W_hz16 hx hc).2
  have hbn := (lowGeometry83W_hz21 hx hc).2
  have hlo := (lowGeometry83W_hz40 hx hc).1
  have hhi := (lowGeometry83W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry83C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (1003 / 2000) (251 / 500) θ := hc

theorem lowGeometry83C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry83C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249 / 500) (997 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry83C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249747 / 1000000) (250247 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry83C_hz0 hx hc) (lowGeometry83C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (250247 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry83C_hz3 hx hc) (lowGeometry83C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (5592930805937081 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry83C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (32215281442197587 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry83C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (1003 / 1000) (251 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry83C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry83C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry83C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (7842494899583933 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry83C_hz7 hx hc) (lowGeometry83C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (63585261040533319 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry83C_hz6 hx hc) (lowGeometry83C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (63585261040533319 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry83C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry83C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (783343 / 100000) (196031 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry83C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (196031 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry83C_hz13 hx hc) (lowGeometry83C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (64565416040533319 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry83C_hz12 hx hc) (lowGeometry83C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (64565416040533319 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry83C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry83C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (251 / 4000000) (θ * x) := bmul (lowGeometry83C_hz0 hx hc) (lowGeometry83C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (63002008032129 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry83C_hz17 hx hc) (lowGeometry83C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (2245030209723317 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry83C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (6465687004003153 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry83C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (6465687004003153 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry83C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry83C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (327981 / 200000) (82077 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry83C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry83C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (734119005557001 / 40000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry83C_hz22 hx hc) (lowGeometry83C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry83C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry83C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry83C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry83C_hz26 hx hc) (lowGeometry83C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry83C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 0 (18935098964065931 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry83C_hz24 hx hc) (lowGeometry83C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (206465687004003153 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry83C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B 1 (33303187429714841 / 31250000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry83C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249 / 500) (66406555734851393 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry83C_hz2 hx hc) (lowGeometry83C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249 / 500) (22007501793715083 / 40000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry83C_hz33 hx hc) (lowGeometry83C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (249 / 500) (22007501793715083 / 40000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry83C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry83C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (193534312995996847 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry83C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (936388257670811851 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry83C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (466321352320064301 / 1000000000000000000) (997 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry83C_hz2 hx hc) (lowGeometry83C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (44738625335599837 / 100000000000000000) (997 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry83C_hz38 hx hc) (lowGeometry83C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry83C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1003 / 2000) (251 / 500) θ) : B (44738625335599837 / 100000000000000000) (997 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry83C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry83C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1003 / 2000) (251 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (420252477 / 1000000000) (293773433 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31792631 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry83C_hz12 hx hc).2
  have hrp := (lowGeometry83C_hz16 hx hc).2
  have hbn := (lowGeometry83C_hz21 hx hc).2
  have hlo := (lowGeometry83C_hz40 hx hc).1
  have hhi := (lowGeometry83C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry84W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (251 / 500) (201 / 400) θ := hc

theorem lowGeometry84W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry84W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (199 / 400) (249 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry84W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (49949 / 200000) (50049 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry84W_hz0 hx hc) (lowGeometry84W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (50049 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry84W_hz3 hx hc) (lowGeometry84W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (699113557031331 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry84W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (2097340671093993 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry84W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (251 / 250) (201 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry84W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry84W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry84W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (201 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry84W_hz7 hx hc) (lowGeometry84W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (3667653171093993 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry84W_hz6 hx hc) (lowGeometry84W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (3667653171093993 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry84W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry84W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (502 / 25) (201 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry84W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (201 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry84W_hz13 hx hc) (lowGeometry84W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (3746168796093993 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry84W_hz12 hx hc) (lowGeometry84W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (3746168796093993 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry84W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry84W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (201 / 3200000) (θ * x) := bmul (lowGeometry84W_hz0 hx hc) (lowGeometry84W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (31564070351759 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry84W_hz17 hx hc) (lowGeometry84W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (5618191021294933 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry84W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (16854573063884799 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry84W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (16854573063884799 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry84W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry84W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (502 / 125) (201 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry84W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry84W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (1797798653909831 / 40000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry84W_hz22 hx hc) (lowGeometry84W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry84W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry84W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry84W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry84W_hz26 hx hc) (lowGeometry84W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry84W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (94491380559287 / 2000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry84W_hz24 hx hc) (lowGeometry84W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (266854573063884799 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry84W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (1139381810641731689 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry84W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (199 / 400) (283706070849791191 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry84W_hz2 hx hc) (lowGeometry84W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (199 / 400) (307328915989612941 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry84W_hz33 hx hc) (lowGeometry84W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (199 / 400) (307328915989612941 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry84W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry84W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (233145426936115201 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry84W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (108713580202446863 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry84W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (216340024602869257 / 500000000000000000) (249 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry84W_hz2 hx hc) (lowGeometry84W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (192717179463047507 / 500000000000000000) (249 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry84W_hz38 hx hc) (lowGeometry84W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (192717179463047507 / 500000000000000000) (249 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry84W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry84W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (251 / 500) (201 / 400) θ) :
    OverlapGuard n θ lowWideWindow (172087747 / 500000000) (8704869 / 12500000) ∧ radiusMinus n θ lowWideWindow ≤ (58682451 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry84W_hz12 hx hc).2
  have hrp := (lowGeometry84W_hz16 hx hc).2
  have hbn := (lowGeometry84W_hz21 hx hc).2
  have hlo := (lowGeometry84W_hz40 hx hc).1
  have hhi := (lowGeometry84W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry84C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (251 / 500) (201 / 400) θ := hc

theorem lowGeometry84C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry84C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (199 / 400) (249 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry84C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (49949 / 200000) (50049 / 200000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry84C_hz0 hx hc) (lowGeometry84C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (50049 / 1600000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry84C_hz3 hx hc) (lowGeometry84C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (699113557031331 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry84C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (32215152708003733 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry84C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (251 / 250) (201 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry84C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry84C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry84C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (7850306149483917 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry84C_hz7 hx hc) (lowGeometry84C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (63616377305939401 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry84C_hz6 hx hc) (lowGeometry84C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (63616377305939401 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry84C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry84C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (196031 / 25000) (156981 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry84C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (156981 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry84C_hz13 hx hc) (lowGeometry84C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (64597508555939401 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry84C_hz12 hx hc) (lowGeometry84C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (64597508555939401 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry84C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry84C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (201 / 3200000) (θ * x) := bmul (lowGeometry84C_hz0 hx hc) (lowGeometry84C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (31564070351759 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry84C_hz17 hx hc) (lowGeometry84C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (5618191021294933 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry84C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (6472156056531763 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry84C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (6472156056531763 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry84C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry84C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (82077 / 50000) (65727 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry84C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry84C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (9185627497320543 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry84C_hz22 hx hc) (lowGeometry84C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry84C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry84C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry84C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry84C_hz26 hx hc) (lowGeometry84C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry84C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 0 (9476979312194353 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry84C_hz24 hx hc) (lowGeometry84C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (206472156056531763 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry84C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B 1 (21315375613316403 / 20000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry84C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (199 / 400) (106150570554315687 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry84C_hz2 hx hc) (lowGeometry84C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (199 / 400) (549706811395967141 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry84C_hz33 hx hc) (lowGeometry84C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (199 / 400) (549706811395967141 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry84C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry84C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (193527843943468237 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry84C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (936325659535184889 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry84C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (232911007809377241 / 500000000000000000) (249 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry84C_hz2 hx hc) (lowGeometry84C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (27929253562147861 / 62500000000000000) (249 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry84C_hz38 hx hc) (lowGeometry84C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry84C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (251 / 500) (201 / 400) θ) : B (27929253562147861 / 62500000000000000) (249 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry84C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry84C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (251 / 500) (201 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (83950611 / 200000000) (587052997 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31808189 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry84C_hz12 hx hc).2
  have hrp := (lowGeometry84C_hz16 hx hc).2
  have hbn := (lowGeometry84C_hz21 hx hc).2
  have hlo := (lowGeometry84C_hz40 hx hc).1
  have hhi := (lowGeometry84C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry85W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (201 / 400) (503 / 1000) θ := hc

theorem lowGeometry85W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry85W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (497 / 1000) (199 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry85W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (99897 / 400000) (100097 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry85W_hz0 hx hc) (lowGeometry85W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (100097 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry85W_hz3 hx hc) (lowGeometry85W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1398220129754253 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry85W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (4194660389262759 / 62500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry85W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (201 / 200) (503 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry85W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry85W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry85W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (503 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry85W_hz7 hx hc) (lowGeometry85W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (7338410389262759 / 62500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry85W_hz6 hx hc) (lowGeometry85W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (7338410389262759 / 62500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry85W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry85W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (201 / 10) (503 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry85W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (503 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry85W_hz13 hx hc) (lowGeometry85W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (7495597889262759 / 62500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry85W_hz12 hx hc) (lowGeometry85W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (7495597889262759 / 62500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry85W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry85W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (503 / 8000000) (θ * x) := bmul (lowGeometry85W_hz0 hx hc) (lowGeometry85W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (31627263581489 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry85W_hz17 hx hc) (lowGeometry85W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1405953048235631 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry85W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (4217859144706893 / 62500000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry85W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (4217859144706893 / 62500000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry85W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry85W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (201 / 50) (503 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry85W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry85W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (44989687707295771 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry85W_hz22 hx hc) (lowGeometry85W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry85W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry85W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry85W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry85W_hz26 hx hc) (lowGeometry85W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry85W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (5911587614592209 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry85W_hz24 hx hc) (lowGeometry85W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (66717859144706893 / 62500000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry85W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (1139525818586354993 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry85W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (497 / 1000) (56691409474671161 / 100000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry85W_hz2 hx hc) (lowGeometry85W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (497 / 1000) (307103397831724641 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry85W_hz33 hx hc) (lowGeometry85W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (497 / 1000) (307103397831724641 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry85W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry85W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (58282140855293107 / 62500000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry85W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (10869785416563923 / 12500000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry85W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (216091334081290789 / 500000000000000000) (199 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry85W_hz2 hx hc) (lowGeometry85W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (192444983622921953 / 500000000000000000) (199 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry85W_hz38 hx hc) (lowGeometry85W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (192444983622921953 / 500000000000000000) (199 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry85W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry85W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (201 / 400) (503 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (343673369 / 1000000000) (695917667 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (117414567 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry85W_hz12 hx hc).2
  have hrp := (lowGeometry85W_hz16 hx hc).2
  have hbn := (lowGeometry85W_hz21 hx hc).2
  have hlo := (lowGeometry85W_hz40 hx hc).1
  have hhi := (lowGeometry85W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry85C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (201 / 400) (503 / 1000) θ := hc

theorem lowGeometry85C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry85C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (497 / 1000) (199 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry85C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (99897 / 400000) (100097 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry85C_hz0 hx hc) (lowGeometry85C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (100097 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry85C_hz3 hx hc) (lowGeometry85C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1398220129754253 / 250000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry85C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (3221499178953799 / 100000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry85C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (201 / 200) (503 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry85C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry85C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry85C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (7858117399383901 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry85C_hz7 hx hc) (lowGeometry85C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (31823730693536797 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry85C_hz6 hx hc) (lowGeometry85C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (31823730693536797 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry85C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry85C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (156981 / 20000) (392843 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry85C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (392843 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry85C_hz13 hx hc) (lowGeometry85C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (32314784443536797 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry85C_hz12 hx hc) (lowGeometry85C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (32314784443536797 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry85C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry85C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (503 / 8000000) (θ * x) := bmul (lowGeometry85C_hz0 hx hc) (lowGeometry85C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (31627263581489 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry85C_hz17 hx hc) (lowGeometry85C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (1405953048235631 / 125000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry85C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (32393158231348939 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry85C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (32393158231348939 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry85C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry85C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (65727 / 40000) (164481 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry85C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry85C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (18389534850357147 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry85C_hz22 hx hc) (lowGeometry85C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry85C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry85C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry85C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry85C_hz26 hx hc) (lowGeometry85C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry85C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 0 (18972818284711481 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry85C_hz24 hx hc) (lowGeometry85C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (1032393158231348939 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry85C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B 1 (66614727072681193 / 62500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry85C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (497 / 1000) (530253227498542297 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry85C_hz2 hx hc) (lowGeometry85C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (497 / 1000) (274613022891626889 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry85C_hz33 hx hc) (lowGeometry85C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (497 / 1000) (274613022891626889 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry85C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry85C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (967606841768651061 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry85C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (936263000237503331 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry85C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (93064542223607831 / 200000000000000000) (199 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry85C_hz2 hx hc) (lowGeometry85C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (223174946416663837 / 500000000000000000) (199 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry85C_hz38 hx hc) (lowGeometry85C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry85C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (201 / 400) (503 / 1000) θ) : B (223174946416663837 / 500000000000000000) (199 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry85C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry85C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (201 / 400) (503 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (209626853 / 500000000) (1832997 / 3125000) ∧ radiusMinus n θ lowCoreWindow ≤ (31823731 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry85C_hz12 hx hc).2
  have hrp := (lowGeometry85C_hz16 hx hc).2
  have hbn := (lowGeometry85C_hz21 hx hc).2
  have hlo := (lowGeometry85C_hz40 hx hc).1
  have hhi := (lowGeometry85C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry86W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (503 / 1000) (1007 / 2000) θ := hc

theorem lowGeometry86W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry86W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (993 / 2000) (497 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry86W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (499479 / 2000000) (500479 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry86W_hz0 hx hc) (lowGeometry86W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (500479 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry86W_hz3 hx hc) (lowGeometry86W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (2796423497076221 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry86W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (8389270491228663 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry86W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (503 / 500) (1007 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry86W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry86W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry86W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1007 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry86W_hz7 hx hc) (lowGeometry86W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (14683020491228663 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry86W_hz6 hx hc) (lowGeometry86W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (14683020491228663 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry86W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry86W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (503 / 25) (1007 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry86W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1007 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry86W_hz13 hx hc) (lowGeometry86W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (14997707991228663 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry86W_hz12 hx hc) (lowGeometry86W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (14997707991228663 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry86W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry86W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1007 / 16000000) (θ * x) := bmul (lowGeometry86W_hz0 hx hc) (lowGeometry86W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (63381168177241 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry86W_hz17 hx hc) (lowGeometry86W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (5629439056302191 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry86W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (16888317168906573 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry86W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (16888317168906573 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry86W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry86W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (503 / 125) (1007 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry86W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry86W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (45034409066845767 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry86W_hz22 hx hc) (lowGeometry86W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry86W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry86W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry86W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry86W_hz26 hx hc) (lowGeometry86W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry86W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (9467942310766369 / 200000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry86W_hz24 hx hc) (lowGeometry86W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (266888317168906573 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry86W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (1139669981460013937 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry86W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (993 / 2000) (566415980785626927 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry86W_hz2 hx hc) (lowGeometry86W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (993 / 2000) (153438923084864693 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry86W_hz33 hx hc) (lowGeometry86W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (993 / 2000) (153438923084864693 / 250000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry86W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry86W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (233111682831093427 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry86W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (27170528336172149 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry86W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (431685354205103103 / 1000000000000000000) (497 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry86W_hz2 hx hc) (lowGeometry86W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (192172821325635629 / 500000000000000000) (497 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry86W_hz38 hx hc) (lowGeometry86W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (192172821325635629 / 500000000000000000) (497 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry86W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry86W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (503 / 1000) (1007 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (34317137 / 100000000) (695445633 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (29366041 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry86W_hz12 hx hc).2
  have hrp := (lowGeometry86W_hz16 hx hc).2
  have hbn := (lowGeometry86W_hz21 hx hc).2
  have hlo := (lowGeometry86W_hz40 hx hc).1
  have hhi := (lowGeometry86W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry86C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (503 / 1000) (1007 / 2000) θ := hc

theorem lowGeometry86C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry86C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (993 / 2000) (497 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry86C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (499479 / 2000000) (500479 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry86C_hz0 hx hc) (lowGeometry86C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (500479 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry86C_hz3 hx hc) (lowGeometry86C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (2796423497076221 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry86C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (16107399343159033 / 500000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry86C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (503 / 500) (1007 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry86C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry86C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry86C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1573185729856777 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry86C_hz7 hx hc) (lowGeometry86C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (31839256641726803 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry86C_hz6 hx hc) (lowGeometry86C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (31839256641726803 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry86C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry86C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (392843 / 50000) (786467 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry86C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (786467 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry86C_hz13 hx hc) (lowGeometry86C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (32330798516726803 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry86C_hz12 hx hc) (lowGeometry86C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (32330798516726803 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry86C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry86C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (1007 / 16000000) (θ * x) := bmul (lowGeometry86C_hz0 hx hc) (lowGeometry86C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (63381168177241 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry86C_hz17 hx hc) (lowGeometry86C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (5629439056302191 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry86C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (32425568964300621 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry86C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (32425568964300621 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry86C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry86C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (164481 / 100000) (329289 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry86C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry86C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (2300976838259151 / 125000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry86C_hz22 hx hc) (lowGeometry86C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry86C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry86C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry86C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry86C_hz26 hx hc) (lowGeometry86C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry86C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 0 (18991677945034257 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry86C_hz24 hx hc) (lowGeometry86C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (1032425568964300621 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry86C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B 1 (532951277725629929 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry86C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (993 / 2000) (10595071401185523 / 20000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry86C_hz2 hx hc) (lowGeometry86C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (993 / 2000) (548745248004310407 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry86C_hz33 hx hc) (lowGeometry86C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (993 / 2000) (548745248004310407 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry86C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry86C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (967574431035699379 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry86C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (936200279594057373 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry86C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (92964687763689897 / 200000000000000000) (497 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry86C_hz2 hx hc) (lowGeometry86C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (111457940218353807 / 250000000000000000) (497 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry86C_hz38 hx hc) (lowGeometry86C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry86C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (503 / 1000) (1007 / 2000) θ) : B (111457940218353807 / 250000000000000000) (497 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry86C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry86C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (503 / 1000) (1007 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (41875443 / 100000000) (146516249 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (31839257 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry86C_hz12 hx hc).2
  have hrp := (lowGeometry86C_hz16 hx hc).2
  have hbn := (lowGeometry86C_hz21 hx hc).2
  have hlo := (lowGeometry86C_hz40 hx hc).1
  have hhi := (lowGeometry86C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry87W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (1007 / 2000) (63 / 125) θ := hc

theorem lowGeometry87W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry87W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (62 / 125) (993 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry87W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (31217 / 125000) (62559 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry87W_hz0 hx hc) (lowGeometry87W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (62559 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry87W_hz3 hx hc) (lowGeometry87W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (1118561576311291 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry87W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (3355684728933873 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry87W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (1007 / 1000) (126 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry87W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry87W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry87W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (63 / 1250) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry87W_hz7 hx hc) (lowGeometry87W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (5875684728933873 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry87W_hz6 hx hc) (lowGeometry87W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (5875684728933873 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry87W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry87W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (1007 / 50) (504 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry87W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (63 / 25000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry87W_hz13 hx hc) (lowGeometry87W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (6001684728933873 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry87W_hz12 hx hc) (lowGeometry87W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (6001684728933873 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry87W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry87W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (63 / 1000000) (θ * x) := bmul (lowGeometry87W_hz0 hx hc) (lowGeometry87W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (127016129032259 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry87W_hz17 hx hc) (lowGeometry87W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (11270143256953703 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry87W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (33810429770861109 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry87W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (33810429770861109 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry87W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry87W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (1007 / 250) (504 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry87W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry87W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (45079130426395763 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry87W_hz22 hx hc) (lowGeometry87W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry87W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry87W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry87W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry87W_hz26 hx hc) (lowGeometry87W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry87W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (23693361095463009 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry87W_hz24 hx hc) (lowGeometry87W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (533810429770861109 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry87W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (1139814299728605761 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry87W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (62 / 125) (565917799815252761 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry87W_hz2 hx hc) (lowGeometry87W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (62 / 125) (613304522006178779 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry87W_hz33 hx hc) (lowGeometry87W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (62 / 125) (613304522006178779 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry87W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry87W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (466189570229138891 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry87W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (108666357695214611 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry87W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (53898513416826447 / 125000000000000000) (993 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry87W_hz2 hx hc) (lowGeometry87W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (191900692571842779 / 500000000000000000) (993 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry87W_hz38 hx hc) (lowGeometry87W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (191900692571842779 / 500000000000000000) (993 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry87W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry87W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1007 / 2000) (63 / 125) θ) :
    OverlapGuard n θ lowWideWindow (342669499 / 1000000000) (86871677 / 125000000) ∧ radiusMinus n θ lowWideWindow ≤ (23502739 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry87W_hz12 hx hc).2
  have hrp := (lowGeometry87W_hz16 hx hc).2
  have hbn := (lowGeometry87W_hz21 hx hc).2
  have hlo := (lowGeometry87W_hz40 hx hc).1
  have hhi := (lowGeometry87W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry87C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (1007 / 2000) (63 / 125) θ := hc

theorem lowGeometry87C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry87C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (62 / 125) (993 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry87C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (31217 / 125000) (62559 / 250000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry87C_hz0 hx hc) (lowGeometry87C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (62559 / 2000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry87C_hz3 hx hc) (lowGeometry87C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (1118561576311291 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry87C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (32214573397765181 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry87C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (1007 / 1000) (126 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry87C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry87C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry87C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (7873739899183869 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry87C_hz7 hx hc) (lowGeometry87C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (63709532994500657 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry87C_hz6 hx hc) (lowGeometry87C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (63709532994500657 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry87C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry87C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (786467 / 100000) (49203 / 6250) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry87C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (49203 / 50000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry87C_hz13 hx hc) (lowGeometry87C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (64693592994500657 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry87C_hz12 hx hc) (lowGeometry87C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (64693592994500657 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry87C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry87C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (63 / 1000000) (θ * x) := bmul (lowGeometry87C_hz0 hx hc) (lowGeometry87C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (127016129032259 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry87C_hz17 hx hc) (lowGeometry87C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (11270143256953703 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry87C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (6491602516005333 / 200000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry87C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (6491602516005333 / 200000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry87C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry87C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (329289 / 200000) (20601 / 12500) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry87C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry87C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (4606523640447317 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry87C_hz22 hx hc) (lowGeometry87C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry87C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry87C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry87C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry87C_hz26 hx hc) (lowGeometry87C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry87C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 0 (19010537605357031 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry87C_hz24 hx hc) (lowGeometry87C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (206491602516005333 / 200000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry87C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B 1 (2131939095481397 / 2000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry87C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (62 / 125) (264626940226628403 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry87C_hz2 hx hc) (lowGeometry87C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (62 / 125) (548264418058613837 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry87C_hz33 hx hc) (lowGeometry87C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (62 / 125) (548264418058613837 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry87C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry87C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (193508397483994667 / 200000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry87C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (936137497420591839 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry87C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (29020262420038347 / 62500000000000000) (993 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry87C_hz2 hx hc) (lowGeometry87C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (445313661115256521 / 1000000000000000000) (993 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry87C_hz38 hx hc) (lowGeometry87C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry87C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1007 / 2000) (63 / 125) θ) : B (445313661115256521 / 1000000000000000000) (993 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry87C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry87C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1007 / 2000) (63 / 125) θ) :
    OverlapGuard n θ lowCoreWindow (418255227 / 1000000000) (117114173 / 200000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63709533 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry87C_hz12 hx hc).2
  have hrp := (lowGeometry87C_hz16 hx hc).2
  have hbn := (lowGeometry87C_hz21 hx hc).2
  have hlo := (lowGeometry87C_hz40 hx hc).1
  have hhi := (lowGeometry87C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry88W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (63 / 125) (1009 / 2000) θ := hc

theorem lowGeometry88W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry88W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (991 / 2000) (62 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry88W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (62433 / 250000) (31279 / 125000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry88W_hz0 hx hc) (lowGeometry88W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (31279 / 1000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry88W_hz3 hx hc) (lowGeometry88W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (279638159055591 / 50000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry88W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (838914477166773 / 12500000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry88W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (126 / 125) (1009 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry88W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry88W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry88W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1009 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry88W_hz7 hx hc) (lowGeometry88W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1469539477166773 / 12500000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry88W_hz6 hx hc) (lowGeometry88W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1469539477166773 / 12500000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry88W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry88W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (504 / 25) (1009 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry88W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1009 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry88W_hz13 hx hc) (lowGeometry88W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1501070727166773 / 12500000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry88W_hz12 hx hc) (lowGeometry88W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1501070727166773 / 12500000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry88W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry88W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1009 / 16000000) (θ * x) := bmul (lowGeometry88W_hz0 hx hc) (lowGeometry88W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (127270433905147 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry88W_hz17 hx hc) (lowGeometry88W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (451256794129723 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry88W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1353770382389169 / 20000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry88W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1353770382389169 / 20000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry88W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry88W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (504 / 125) (1009 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry88W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry88W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (45123851785945759 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry88W_hz22 hx hc) (lowGeometry88W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry88W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry88W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry88W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry88W_hz26 hx hc) (lowGeometry88W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry88W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (47433732828020191 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry88W_hz24 hx hc) (lowGeometry88W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (21353770382389169 / 20000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry88W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (1139958773859502193 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry88W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (991 / 2000) (4417340248705571 / 7812500000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry88W_hz2 hx hc) (lowGeometry88W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (991 / 2000) (612853284662333279 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry88W_hz33 hx hc) (lowGeometry88W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (991 / 2000) (612853284662333279 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry88W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry88W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (18646229617610831 / 20000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry88W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (108650587172708549 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry88W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (26918182972038543 / 62500000000000000) (62 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry88W_hz2 hx hc) (lowGeometry88W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (383257194724596497 / 1000000000000000000) (62 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry88W_hz38 hx hc) (lowGeometry88W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (383257194724596497 / 1000000000000000000) (62 / 125) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry88W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry88W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (63 / 125) (1009 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (171083877 / 500000000) (347250509 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (117563159 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry88W_hz12 hx hc).2
  have hrp := (lowGeometry88W_hz16 hx hc).2
  have hbn := (lowGeometry88W_hz21 hx hc).2
  have hlo := (lowGeometry88W_hz40 hx hc).1
  have hhi := (lowGeometry88W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry88C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (63 / 125) (1009 / 2000) θ := hc

theorem lowGeometry88C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry88C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (991 / 2000) (62 / 125) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry88C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (62433 / 250000) (31279 / 125000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry88C_hz0 hx hc) (lowGeometry88C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (31279 / 1000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry88C_hz3 hx hc) (lowGeometry88C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (279638159055591 / 50000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry88C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (8053578980801021 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry88C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (126 / 125) (1009 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry88C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry88C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry88C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (7881551149083853 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry88C_hz7 hx hc) (lowGeometry88C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (7967565064942437 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry88C_hz6 hx hc) (lowGeometry88C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (7967565064942437 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry88C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry88C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (49203 / 6250) (788029 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry88C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (788029 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry88C_hz13 hx hc) (lowGeometry88C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (8090694596192437 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry88C_hz12 hx hc) (lowGeometry88C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (8090694596192437 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry88C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry88C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (1009 / 16000000) (θ * x) := bmul (lowGeometry88C_hz0 hx hc) (lowGeometry88C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (127270433905147 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry88C_hz17 hx hc) (lowGeometry88C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (451256794129723 / 40000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry88C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (4061311147167507 / 125000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry88C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (4061311147167507 / 125000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry88C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry88C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (20601 / 12500) (329943 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry88C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry88C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (18444374417505329 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry88C_hz22 hx hc) (lowGeometry88C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry88C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry88C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry88C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry88C_hz26 hx hc) (lowGeometry88C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry88C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 0 (9514698632839903 / 500000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry88C_hz24 hx hc) (lowGeometry88C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (129061311147167507 / 125000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry88C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B 1 (266509152560415741 / 250000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry88C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (991 / 2000) (528754158679864831 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry88C_hz2 hx hc) (lowGeometry88C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (991 / 2000) (547783555945544637 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry88C_hz33 hx hc) (lowGeometry88C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (991 / 2000) (547783555945544637 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry88C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry88C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (120938688852832493 / 125000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry88C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (936074653532302739 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry88C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (463824990825256007 / 1000000000000000000) (62 / 125) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry88C_hz2 hx hc) (lowGeometry88C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (444795593559576201 / 1000000000000000000) (62 / 125) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry88C_hz38 hx hc) (lowGeometry88C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry88C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (63 / 125) (1009 / 2000) θ) : B (444795593559576201 / 1000000000000000000) (62 / 125) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry88C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry88C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (63 / 125) (1009 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (417756097 / 1000000000) (292538323 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63740521 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry88C_hz12 hx hc).2
  have hrp := (lowGeometry88C_hz16 hx hc).2
  have hbn := (lowGeometry88C_hz21 hx hc).2
  have hlo := (lowGeometry88C_hz40 hx hc).1
  have hhi := (lowGeometry88C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry89W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (1009 / 2000) (101 / 200) θ := hc

theorem lowGeometry89W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry89W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99 / 200) (991 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry89W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99891 / 400000) (100091 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry89W_hz0 hx hc) (lowGeometry89W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (100091 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry89W_hz3 hx hc) (lowGeometry89W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (699089111585569 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry89W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (2097267334756707 / 31250000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry89W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (1009 / 1000) (101 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry89W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry89W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry89W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (101 / 2000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry89W_hz7 hx hc) (lowGeometry89W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (3675392334756707 / 31250000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry89W_hz6 hx hc) (lowGeometry89W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (3675392334756707 / 31250000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry89W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry89W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (1009 / 50) (101 / 5) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry89W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (101 / 40000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry89W_hz13 hx hc) (lowGeometry89W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (3754298584756707 / 31250000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry89W_hz12 hx hc) (lowGeometry89W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (3754298584756707 / 31250000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry89W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry89W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (101 / 1600000) (θ * x) := bmul (lowGeometry89W_hz0 hx hc) (lowGeometry89W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (127525252525253 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry89W_hz17 hx hc) (lowGeometry89W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (2258541587177469 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry89W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (6775624761532407 / 100000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry89W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (6775624761532407 / 100000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry89W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry89W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (1009 / 250) (101 / 25) (θ * (8 : ℝ)) := bmul (lowGeometry89W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry89W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (22584286572747877 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry89W_hz22 hx hc) (lowGeometry89W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry89W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry89W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry89W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry89W_hz26 hx hc) (lowGeometry89W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry89W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (47480743465114363 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry89W_hz24 hx hc) (lowGeometry89W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (106775624761532407 / 100000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry89W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (1140103404321557249 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry89W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99 / 200) (564921236841331617 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry89W_hz2 hx hc) (lowGeometry89W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99 / 200) (30620099015322299 / 50000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry89W_hz33 hx hc) (lowGeometry89W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99 / 200) (30620099015322299 / 50000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry89W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry89W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (93224375238467593 / 100000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry89W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (108634801732532621 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry89W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (430193814860829179 / 1000000000000000000) (991 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry89W_hz2 hx hc) (lowGeometry89W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (1494972935139511 / 3906250000000000) (991 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry89W_hz38 hx hc) (lowGeometry89W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (1494972935139511 / 3906250000000000) (991 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry89W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry89W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1009 / 2000) (101 / 200) θ) :
    OverlapGuard n θ lowWideWindow (341666137 / 1000000000) (347014219 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (23522511 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry89W_hz12 hx hc).2
  have hrp := (lowGeometry89W_hz16 hx hc).2
  have hbn := (lowGeometry89W_hz21 hx hc).2
  have hlo := (lowGeometry89W_hz40 hx hc).1
  have hhi := (lowGeometry89W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry89C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (1009 / 2000) (101 / 200) θ := hc

theorem lowGeometry89C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry89C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99 / 200) (991 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry89C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99891 / 400000) (100091 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry89C_hz0 hx hc) (lowGeometry89C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (100091 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry89C_hz3 hx hc) (lowGeometry89C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (699089111585569 / 125000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry89C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1610701313093151 / 50000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry89C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (1009 / 1000) (101 / 100) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry89C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry89C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry89C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (7889362398983837 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry89C_hz7 hx hc) (lowGeometry89C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1992858620556199 / 31250000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry89C_hz6 hx hc) (lowGeometry89C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1992858620556199 / 31250000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry89C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry89C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (788029 / 100000) (78881 / 10000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry89C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (78881 / 80000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry89C_hz13 hx hc) (lowGeometry89C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (2023671511181199 / 31250000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry89C_hz12 hx hc) (lowGeometry89C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (2023671511181199 / 31250000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry89C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry89C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (101 / 1600000) (θ * x) := bmul (lowGeometry89C_hz0 hx hc) (lowGeometry89C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (127525252525253 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry89C_hz17 hx hc) (lowGeometry89C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (2258541587177469 / 200000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry89C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (16261499427677777 / 500000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry89C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (16261499427677777 / 500000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry89C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry89C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (329943 / 200000) (33027 / 20000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry89C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry89C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (1846265427322139 / 100000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry89C_hz22 hx hc) (lowGeometry89C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry89C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry89C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry89C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry89C_hz26 hx hc) (lowGeometry89C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry89C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 0 (19048256926002581 / 1000000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry89C_hz24 hx hc) (lowGeometry89C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (516261499427677777 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry89C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B 1 (1066103743165256567 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry89C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99 / 200) (528254404738384629 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry89C_hz2 hx hc) (lowGeometry89C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99 / 200) (54730266166438721 / 100000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry89C_hz33 hx hc) (lowGeometry89C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (99 / 200) (54730266166438721 / 100000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry89C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry89C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (483738500572322223 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry89C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (18720234954876687 / 20000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry89C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (463325815133198003 / 1000000000000000000) (991 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry89C_hz2 hx hc) (lowGeometry89C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (222138779103597711 / 500000000000000000) (991 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry89C_hz38 hx hc) (lowGeometry89C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry89C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1009 / 2000) (101 / 200) θ) : B (222138779103597711 / 500000000000000000) (991 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry89C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry89C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1009 / 2000) (101 / 200) θ) :
    OverlapGuard n θ lowCoreWindow (5215713 / 12500000) (584582341 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15942869 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry89C_hz12 hx hc).2
  have hrp := (lowGeometry89C_hz16 hx hc).2
  have hbn := (lowGeometry89C_hz21 hx hc).2
  have hlo := (lowGeometry89C_hz40 hx hc).1
  have hhi := (lowGeometry89C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry90W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (101 / 200) (1011 / 2000) θ := hc

theorem lowGeometry90W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry90W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (989 / 2000) (99 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry90W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (99889 / 400000) (100089 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry90W_hz0 hx hc) (lowGeometry90W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (100089 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry90W_hz3 hx hc) (lowGeometry90W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (5592657016123911 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry90W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (16777971048371733 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry90W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (101 / 100) (1011 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry90W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry90W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry90W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1011 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry90W_hz7 hx hc) (lowGeometry90W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (29415471048371733 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry90W_hz6 hx hc) (lowGeometry90W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (29415471048371733 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry90W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry90W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (101 / 5) (1011 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry90W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1011 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry90W_hz13 hx hc) (lowGeometry90W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (30047346048371733 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry90W_hz12 hx hc) (lowGeometry90W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (30047346048371733 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry90W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry90W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1011 / 16000000) (θ * x) := bmul (lowGeometry90W_hz0 hx hc) (lowGeometry90W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (127780586450961 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry90W_hz17 hx hc) (lowGeometry90W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (11304007539406589 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry90W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (33912022618219767 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry90W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (33912022618219767 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry90W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry90W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (101 / 25) (1011 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry90W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry90W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (180853178020183 / 4000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry90W_hz22 hx hc) (lowGeometry90W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry90W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry90W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry90W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry90W_hz26 hx hc) (lowGeometry90W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry90W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (5940969262776067 / 125000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry90W_hz24 hx hc) (lowGeometry90W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (533912022618219767 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry90W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (228049638317022733 / 200000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry90W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (989 / 2000) (112884570966926253 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry90W_hz2 hx hc) (lowGeometry90W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (989 / 2000) (611950608936839801 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry90W_hz33 hx hc) (lowGeometry90W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (989 / 2000) (611950608936839801 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry90W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry90W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (466087977381780233 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry90W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (108619001329919441 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry90W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (107424192315290327 / 250000000000000000) (99 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry90W_hz2 hx hc) (lowGeometry90W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (95542253789738193 / 250000000000000000) (99 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry90W_hz38 hx hc) (lowGeometry90W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (95542253789738193 / 250000000000000000) (99 / 200) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry90W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry90W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (101 / 200) (1011 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (170582323 / 500000000) (693555677 / 1000000000) ∧ radiusMinus n θ lowWideWindow ≤ (23532377 / 200000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry90W_hz12 hx hc).2
  have hrp := (lowGeometry90W_hz16 hx hc).2
  have hbn := (lowGeometry90W_hz21 hx hc).2
  have hlo := (lowGeometry90W_hz40 hx hc).1
  have hhi := (lowGeometry90W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry90C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (101 / 200) (1011 / 2000) θ := hc

theorem lowGeometry90C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry90C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (989 / 2000) (99 / 200) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry90C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (99889 / 400000) (100089 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry90C_hz0 hx hc) (lowGeometry90C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (100089 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry90C_hz3 hx hc) (lowGeometry90C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (5592657016123911 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry90C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (31458695715697 / 976562500000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry90C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (101 / 100) (1011 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry90C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry90C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry90C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (7897173648883821 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry90C_hz7 hx hc) (lowGeometry90C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (15950599752102253 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry90C_hz6 hx hc) (lowGeometry90C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (15950599752102253 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry90C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry90C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (78881 / 10000) (789591 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry90C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (789591 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry90C_hz13 hx hc) (lowGeometry90C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (16197346939602253 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry90C_hz12 hx hc) (lowGeometry90C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (16197346939602253 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry90C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry90C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (1011 / 16000000) (θ * x) := bmul (lowGeometry90C_hz0 hx hc) (lowGeometry90C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (127780586450961 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry90C_hz17 hx hc) (lowGeometry90C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (11304007539406589 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry90C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (32555541713490977 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry90C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (32555541713490977 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry90C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry90C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (33027 / 20000) (330597 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry90C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry90C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (18480934128937451 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry90C_hz22 hx hc) (lowGeometry90C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry90C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry90C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry90C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry90C_hz26 hx hc) (lowGeometry90C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry90C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 0 (4766779146581339 / 250000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry90C_hz24 hx hc) (lowGeometry90C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (1032555541713490977 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry90C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B 1 (533085473361620403 / 500000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry90C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (989 / 2000) (527754618628004199 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry90C_hz2 hx hc) (lowGeometry90C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (989 / 2000) (109364347042865911 / 200000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry90C_hz33 hx hc) (lowGeometry90C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (989 / 2000) (109364347042865911 / 200000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry90C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry90C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (967444458286509023 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry90C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (935948779869276897 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry90C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (18513066865814297 / 40000000000000000) (99 / 200) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry90C_hz2 hx hc) (lowGeometry90C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (443759555059032069 / 1000000000000000000) (99 / 200) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry90C_hz38 hx hc) (lowGeometry90C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry90C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (101 / 200) (1011 / 2000) θ) : B (443759555059032069 / 1000000000000000000) (99 / 200) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry90C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry90C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (101 / 200) (1011 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (83351611 / 200000000) (146021987 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (79753 / 1250000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry90C_hz12 hx hc).2
  have hrp := (lowGeometry90C_hz16 hx hc).2
  have hbn := (lowGeometry90C_hz21 hx hc).2
  have hlo := (lowGeometry90C_hz40 hx hc).1
  have hhi := (lowGeometry90C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry91W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (1011 / 2000) (253 / 500) θ := hc

theorem lowGeometry91W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry91W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (247 / 500) (989 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry91W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (249717 / 1000000) (250217 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry91W_hz0 hx hc) (lowGeometry91W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (250217 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry91W_hz3 hx hc) (lowGeometry91W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (2796297775631201 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry91W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (8388893326893603 / 125000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry91W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (1011 / 1000) (253 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry91W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry91W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry91W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (253 / 5000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry91W_hz7 hx hc) (lowGeometry91W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (14713893326893603 / 125000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry91W_hz6 hx hc) (lowGeometry91W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (14713893326893603 / 125000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry91W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry91W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (1011 / 50) (506 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry91W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (253 / 100000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry91W_hz13 hx hc) (lowGeometry91W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (15030143326893603 / 125000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry91W_hz12 hx hc) (lowGeometry91W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (15030143326893603 / 125000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry91W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry91W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (253 / 4000000) (θ * x) := bmul (lowGeometry91W_hz0 hx hc) (lowGeometry91W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (32009109311741 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry91W_hz17 hx hc) (lowGeometry91W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (565765934921333 / 50000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry91W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1697297804763999 / 25000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry91W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1697297804763999 / 25000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry91W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry91W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (1011 / 250) (506 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry91W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry91W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (22629007932297873 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry91W_hz22 hx hc) (lowGeometry91W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry91W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry91W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry91W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry91W_hz26 hx hc) (lowGeometry91W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry91W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (11893691184825677 / 250000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry91W_hz24 hx hc) (lowGeometry91W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (26697297804763999 / 25000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry91W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (1824629017795217 / 1600000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry91W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (247 / 500) (112784881162466851 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry91W_hz2 hx hc) (lowGeometry91W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (247 / 500) (611499170551636963 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry91W_hz33 hx hc) (lowGeometry91W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (247 / 500) (611499170551636963 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry91W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry91W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (23302702195236001 / 25000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry91W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (27150796479992837 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry91W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (429199790755726767 / 1000000000000000000) (989 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry91W_hz2 hx hc) (lowGeometry91W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (381625026016424059 / 1000000000000000000) (989 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry91W_hz38 hx hc) (lowGeometry91W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (381625026016424059 / 1000000000000000000) (989 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry91W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry91W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1011 / 2000) (253 / 500) θ) :
    OverlapGuard n θ lowWideWindow (170331641 / 500000000) (346541367 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (117711147 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry91W_hz12 hx hc).2
  have hrp := (lowGeometry91W_hz16 hx hc).2
  have hbn := (lowGeometry91W_hz21 hx hc).2
  have hlo := (lowGeometry91W_hz40 hx hc).1
  have hhi := (lowGeometry91W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry91C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (1011 / 2000) (253 / 500) θ := hc

theorem lowGeometry91C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry91C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (247 / 500) (989 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry91C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (249717 / 1000000) (250217 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry91C_hz0 hx hc) (lowGeometry91C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (250217 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry91C_hz3 hx hc) (lowGeometry91C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (2796297775631201 / 500000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry91C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (8053337593817859 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry91C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (1011 / 1000) (253 / 250) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry91C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry91C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry91C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1580996979756761 / 50000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry91C_hz7 hx hc) (lowGeometry91C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (249348788946901 / 3906250000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry91C_hz6 hx hc) (lowGeometry91C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (249348788946901 / 3906250000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry91C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry91C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (789591 / 100000) (197593 / 25000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry91C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (197593 / 200000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry91C_hz13 hx hc) (lowGeometry91C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (253208027228151 / 3906250000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry91C_hz12 hx hc) (lowGeometry91C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (253208027228151 / 3906250000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry91C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry91C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (253 / 4000000) (θ * x) := bmul (lowGeometry91C_hz0 hx hc) (lowGeometry91C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (32009109311741 / 250000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry91C_hz17 hx hc) (lowGeometry91C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (565765934921333 / 50000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry91C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (32588117851468781 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry91C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (32588117851468781 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry91C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry91C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (330597 / 200000) (82731 / 50000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry91C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry91C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (18499213984653511 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry91C_hz22 hx hc) (lowGeometry91C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry91C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry91C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry91C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry91C_hz26 hx hc) (lowGeometry91C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry91C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 0 (1908597624664813 / 100000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry91C_hz24 hx hc) (lowGeometry91C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (1032588117851468781 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry91C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B 1 (1066238221128038781 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry91C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (247 / 500) (263627400173907589 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry91C_hz2 hx hc) (lowGeometry91C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (247 / 500) (136585194148615827 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry91C_hz33 hx hc) (lowGeometry91C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (247 / 500) (136585194148615827 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry91C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry91C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (967411882148531219 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry91C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (116985718715270457 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry91C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (231163780181374423 / 500000000000000000) (989 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry91C_hz2 hx hc) (lowGeometry91C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (110810396029025179 / 250000000000000000) (989 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry91C_hz38 hx hc) (lowGeometry91C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry91C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1011 / 2000) (253 / 500) θ) : B (110810396029025179 / 250000000000000000) (989 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry91C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry91C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1011 / 2000) (253 / 500) θ) :
    OverlapGuard n θ lowCoreWindow (52032393 / 125000000) (145898367 / 250000000) ∧ radiusMinus n θ lowCoreWindow ≤ (6383329 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry91C_hz12 hx hc).2
  have hrp := (lowGeometry91C_hz16 hx hc).2
  have hbn := (lowGeometry91C_hz21 hx hc).2
  have hlo := (lowGeometry91C_hz40 hx hc).1
  have hhi := (lowGeometry91C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry92W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (253 / 500) (1013 / 2000) θ := hc

theorem lowGeometry92W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry92W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (987 / 2000) (247 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry92W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (249711 / 1000000) (250211 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry92W_hz0 hx hc) (lowGeometry92W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (250211 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry92W_hz3 hx hc) (lowGeometry92W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (5592528497915769 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry92W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (16777585493747307 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry92W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (253 / 250) (1013 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry92W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry92W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry92W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1013 / 20000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry92W_hz7 hx hc) (lowGeometry92W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (29440085493747307 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry92W_hz6 hx hc) (lowGeometry92W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (29440085493747307 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry92W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry92W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (506 / 25) (1013 / 50) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry92W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1013 / 400000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry92W_hz13 hx hc) (lowGeometry92W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (30073210493747307 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry92W_hz12 hx hc) (lowGeometry92W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (30073210493747307 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry92W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry92W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1013 / 16000000) (θ * x) := bmul (lowGeometry92W_hz0 hx hc) (lowGeometry92W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (16036600810537 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry92W_hz17 hx hc) (lowGeometry92W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (5663320723839857 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry92W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (16989962171519571 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry92W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (16989962171519571 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry92W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry92W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (506 / 125) (1013 / 250) (θ * (8 : ℝ)) := bmul (lowGeometry92W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry92W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (22651368612072871 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry92W_hz22 hx hc) (lowGeometry92W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry92W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry92W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry92W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry92W_hz26 hx hc) (lowGeometry92W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry92W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (47621775376396881 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry92W_hz24 hx hc) (lowGeometry92W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (266989962171519571 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry92W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (45621529536223649 / 40000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry92W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (987 / 2000) (281712944886181033 / 500000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry92W_hz2 hx hc) (lowGeometry92W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (987 / 2000) (611047665148758947 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry92W_hz33 hx hc) (lowGeometry92W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (987 / 2000) (611047665148758947 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry92W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry92W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (233010037828480429 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry92W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (108587355457659761 / 125000000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry92W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (13396964979588773 / 31250000000000000) (247 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry92W_hz2 hx hc) (lowGeometry92W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (76216220794088771 / 200000000000000000) (247 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry92W_hz38 hx hc) (lowGeometry92W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (76216220794088771 / 200000000000000000) (247 / 500) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry92W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry92W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (253 / 500) (1013 / 2000) θ) :
    OverlapGuard n θ lowWideWindow (85040511 / 250000000) (69260961 / 100000000) ∧ radiusMinus n θ lowWideWindow ≤ (58880171 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry92W_hz12 hx hc).2
  have hrp := (lowGeometry92W_hz16 hx hc).2
  have hbn := (lowGeometry92W_hz21 hx hc).2
  have hlo := (lowGeometry92W_hz40 hx hc).1
  have hhi := (lowGeometry92W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry92C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (253 / 500) (1013 / 2000) θ := hc

theorem lowGeometry92C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry92C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (987 / 2000) (247 / 500) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry92C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (249711 / 1000000) (250211 / 1000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry92C_hz0 hx hc) (lowGeometry92C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (250211 / 8000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry92C_hz3 hx hc) (lowGeometry92C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (5592528497915769 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry92C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (3221296414799483 / 100000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry92C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (253 / 250) (1013 / 1000) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry92C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry92C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry92C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (7912796148683789 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry92C_hz7 hx hc) (lowGeometry92C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (31932074371364993 / 500000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry92C_hz6 hx hc) (lowGeometry92C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (31932074371364993 / 500000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry92C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry92C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (197593 / 25000) (791153 / 100000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry92C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (791153 / 800000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry92C_hz13 hx hc) (lowGeometry92C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (32426544996364993 / 500000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry92C_hz12 hx hc) (lowGeometry92C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (32426544996364993 / 500000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry92C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry92C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (1013 / 16000000) (θ * x) := bmul (lowGeometry92C_hz0 hx hc) (lowGeometry92C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (16036600810537 / 125000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry92C_hz17 hx hc) (lowGeometry92C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (5663320723839857 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry92C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (32620727369317577 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry92C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (32620727369317577 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry92C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry92C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (82731 / 50000) (331251 / 200000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry92C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry92C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (4629373460092393 / 250000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry92C_hz22 hx hc) (lowGeometry92C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry92C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry92C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry92C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry92C_hz26 hx hc) (lowGeometry92C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry92C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 0 (3820967181394181 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry92C_hz24 hx hc) (lowGeometry92C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (1032620727369317577 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry92C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B 1 (1066305566592738499 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry92C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (987 / 2000) (526754949896812819 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry92C_hz2 hx hc) (lowGeometry92C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (987 / 2000) (136464946450945931 / 250000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry92C_hz33 hx hc) (lowGeometry92C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (987 / 2000) (136464946450945931 / 250000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry92C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry92C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (967379272630682423 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry92C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (93582265711546819 / 100000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry92C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (461828481286483551 / 1000000000000000000) (247 / 500) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry92C_hz2 hx hc) (lowGeometry92C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (221361822689756323 / 500000000000000000) (247 / 500) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry92C_hz38 hx hc) (lowGeometry92C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry92C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (253 / 500) (1013 / 2000) θ) : B (221361822689756323 / 500000000000000000) (247 / 500) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry92C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry92C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (253 / 500) (1013 / 2000) θ) :
    OverlapGuard n θ lowCoreWindow (25985019 / 62500000) (583098901 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (63864149 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry92C_hz12 hx hc).2
  have hrp := (lowGeometry92C_hz16 hx hc).2
  have hbn := (lowGeometry92C_hz21 hx hc).2
  have hlo := (lowGeometry92C_hz40 hx hc).1
  have hhi := (lowGeometry92C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry93W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (1013 / 2000) (507 / 1000) θ := hc

theorem lowGeometry93W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry93W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (493 / 1000) (987 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry93W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (499409 / 2000000) (500409 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry93W_hz0 hx hc) (lowGeometry93W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (500409 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry93W_hz3 hx hc) (lowGeometry93W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (1118491171176599 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry93W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (3355473513529797 / 50000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry93W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (1013 / 1000) (507 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry93W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry93W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry93W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (507 / 10000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry93W_hz7 hx hc) (lowGeometry93W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (5890473513529797 / 50000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry93W_hz6 hx hc) (lowGeometry93W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (5890473513529797 / 50000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry93W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry93W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (1013 / 50) (507 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry93W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (507 / 200000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry93W_hz13 hx hc) (lowGeometry93W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (6017223513529797 / 50000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry93W_hz12 hx hc) (lowGeometry93W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (6017223513529797 / 50000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry93W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry93W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (507 / 8000000) (θ * x) := bmul (lowGeometry93W_hz0 hx hc) (lowGeometry93W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (64274847870183 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry93W_hz17 hx hc) (lowGeometry93W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (5668987911002413 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry93W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (17006963733007239 / 250000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry93W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (17006963733007239 / 250000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry93W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry93W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (1013 / 250) (507 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry93W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry93W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (22673729291847869 / 500000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry93W_hz22 hx hc) (lowGeometry93W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry93W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry93W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry93W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry93W_hz26 hx hc) (lowGeometry93W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry93W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (23834393006745527 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry93W_hz24 hx hc) (lowGeometry93W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (267006963733007239 / 250000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry93W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (1140683498910711089 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry93W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (493 / 1000) (562927306712435923 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry93W_hz2 hx hc) (lowGeometry93W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (493 / 1000) (610596092725926977 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry93W_hz33 hx hc) (lowGeometry93W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (493 / 1000) (610596092725926977 / 1000000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry93W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry93W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (232993036266992761 / 250000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry93W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (13571438737228051 / 15625000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry93W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (85641207007403893 / 200000000000000000) (987 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry93W_hz2 hx hc) (lowGeometry93W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (380537249023528411 / 1000000000000000000) (987 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry93W_hz38 hx hc) (lowGeometry93W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (380537249023528411 / 1000000000000000000) (987 / 2000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry93W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry93W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1013 / 2000) (507 / 1000) θ) :
    OverlapGuard n θ lowWideWindow (339660933 / 1000000000) (138427261 / 200000000) ∧ radiusMinus n θ lowWideWindow ≤ (117809471 / 1000000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry93W_hz12 hx hc).2
  have hrp := (lowGeometry93W_hz16 hx hc).2
  have hbn := (lowGeometry93W_hz21 hx hc).2
  have hlo := (lowGeometry93W_hz40 hx hc).1
  have hhi := (lowGeometry93W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry93C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (1013 / 2000) (507 / 1000) θ := hc

theorem lowGeometry93C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry93C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (493 / 1000) (987 / 2000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry93C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (499409 / 2000000) (500409 / 2000000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry93C_hz0 hx hc) (lowGeometry93C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (500409 / 16000000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry93C_hz3 hx hc) (lowGeometry93C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (1118491171176599 / 200000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry93C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (8053136432471513 / 250000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry93C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (1013 / 1000) (507 / 500) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry93C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry93C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry93C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (7920607398583773 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry93C_hz7 hx hc) (lowGeometry93C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (7986871915527643 / 125000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry93C_hz6 hx hc) (lowGeometry93C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (7986871915527643 / 125000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry93C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry93C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (791153 / 100000) (395967 / 50000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry93C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (395967 / 400000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry93C_hz13 hx hc) (lowGeometry93C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (8110611603027643 / 125000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry93C_hz12 hx hc) (lowGeometry93C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (8110611603027643 / 125000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry93C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry93C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (507 / 8000000) (θ * x) := bmul (lowGeometry93C_hz0 hx hc) (lowGeometry93C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (64274847870183 / 500000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry93C_hz17 hx hc) (lowGeometry93C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (5668987911002413 / 500000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry93C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (32653370367373899 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry93C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (32653370367373899 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry93C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry93C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (331251 / 200000) (165789 / 100000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry93C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry93C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (18535773696085633 / 1000000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry93C_hz22 hx hc) (lowGeometry93C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry93C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry93C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry93C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry93C_hz26 hx hc) (lowGeometry93C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry93C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 0 (239046194591171 / 12500000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry93C_hz24 hx hc) (lowGeometry93C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (1032653370367373899 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry93C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B 1 (106637298333109669 / 100000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry93C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (493 / 1000) (526255067273896217 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry93C_hz2 hx hc) (lowGeometry93C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (493 / 1000) (545378762841189897 / 1000000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry93C_hz33 hx hc) (lowGeometry93C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (493 / 1000) (545378762841189897 / 1000000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry93C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry93C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (967346629632626101 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry93C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (935759501861601093 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry93C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (230664717208884669 / 500000000000000000) (987 / 2000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry93C_hz2 hx hc) (lowGeometry93C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (221102869425237829 / 500000000000000000) (987 / 2000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry93C_hz38 hx hc) (lowGeometry93C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry93C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (1013 / 2000) (507 / 1000) θ) : B (221102869425237829 / 500000000000000000) (987 / 2000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry93C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry93C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (1013 / 2000) (507 / 1000) θ) :
    OverlapGuard n θ lowCoreWindow (207630769 / 500000000) (582604247 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (998359 / 15625000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry93C_hz12 hx hc).2
  have hrp := (lowGeometry93C_hz16 hx hc).2
  have hbn := (lowGeometry93C_hz21 hx hc).2
  have hlo := (lowGeometry93C_hz40 hx hc).1
  have hhi := (lowGeometry93C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry94W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (507 / 1000) (203 / 400) θ := hc

theorem lowGeometry94W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry94W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (197 / 400) (493 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry94W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (99879 / 400000) (100079 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry94W_hz0 hx hc) (lowGeometry94W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (100079 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry94W_hz3 hx hc) (lowGeometry94W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (5592377624946299 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry94W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (16777132874838897 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry94W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (507 / 500) (203 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry94W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry94W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry94W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (203 / 4000) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry94W_hz7 hx hc) (lowGeometry94W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (29464632874838897 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry94W_hz6 hx hc) (lowGeometry94W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (29464632874838897 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry94W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry94W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (507 / 25) (203 / 10) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry94W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (203 / 80000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry94W_hz13 hx hc) (lowGeometry94W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (30099007874838897 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry94W_hz12 hx hc) (lowGeometry94W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (30099007874838897 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry94W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry94W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (203 / 3200000) (θ * x) := bmul (lowGeometry94W_hz0 hx hc) (lowGeometry94W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (25761421319797 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry94W_hz17 hx hc) (lowGeometry94W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (11349321856348291 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry94W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (34047965569044873 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry94W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (34047965569044873 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry94W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry94W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (507 / 125) (203 / 50) (θ * (8 : ℝ)) := bmul (lowGeometry94W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry94W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (45392179943245733 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry94W_hz22 hx hc) (lowGeometry94W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry94W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry94W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry94W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry94W_hz26 hx hc) (lowGeometry94W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry94W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (23857898325292613 / 500000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry94W_hz24 hx hc) (lowGeometry94W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (534047965569044873 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry94W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (1140828918113742953 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry94W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (197 / 400) (140607164157518819 / 250000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry94W_hz2 hx hc) (lowGeometry94W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (197 / 400) (305072226640330251 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry94W_hz33 hx hc) (lowGeometry94W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (197 / 400) (305072226640330251 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry94W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry94W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (465952034430955127 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry94W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (27138912298793249 / 31250000000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry94W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (106927314457245401 / 250000000000000000) (493 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry94W_hz2 hx hc) (lowGeometry94W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (189996730589198189 / 500000000000000000) (493 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry94W_hz38 hx hc) (lowGeometry94W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (189996730589198189 / 500000000000000000) (493 / 1000) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry94W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry94W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (507 / 1000) (203 / 400) θ) :
    OverlapGuard n θ lowWideWindow (339159949 / 1000000000) (345831409 / 500000000) ∧ radiusMinus n θ lowWideWindow ≤ (29464633 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry94W_hz12 hx hc).2
  have hrp := (lowGeometry94W_hz16 hx hc).2
  have hbn := (lowGeometry94W_hz21 hx hc).2
  have hlo := (lowGeometry94W_hz40 hx hc).1
  have hhi := (lowGeometry94W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry94C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (507 / 1000) (203 / 400) θ := hc

theorem lowGeometry94C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry94C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (197 / 400) (493 / 1000) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry94C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (99879 / 400000) (100079 / 400000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry94C_hz0 hx hc) (lowGeometry94C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (100079 / 3200000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry94C_hz3 hx hc) (lowGeometry94C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (5592377624946299 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry94C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (32212095119690683 / 1000000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry94C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (507 / 500) (203 / 200) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry94C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry94C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry94C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (7928418648483757 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry94C_hz7 hx hc) (lowGeometry94C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (63925769713625711 / 1000000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry94C_hz6 hx hc) (lowGeometry94C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (63925769713625711 / 1000000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry94C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry94C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (395967 / 50000) (158543 / 20000) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry94C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (158543 / 160000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry94C_hz13 hx hc) (lowGeometry94C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (64916663463625711 / 1000000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry94C_hz12 hx hc) (lowGeometry94C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (64916663463625711 / 1000000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry94C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry94C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (203 / 3200000) (θ * x) := bmul (lowGeometry94C_hz0 hx hc) (lowGeometry94C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (25761421319797 / 200000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry94C_hz17 hx hc) (lowGeometry94C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (11349321856348291 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry94C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (32686046946283079 / 1000000000000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry94C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (32686046946283079 / 1000000000000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry94C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry94C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (165789 / 100000) (66381 / 40000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry94C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry94C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (9277026775900847 / 500000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry94C_hz22 hx hc) (lowGeometry94C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry94C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry94C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry94C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry94C_hz26 hx hc) (lowGeometry94C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry94C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 0 (3828511045523291 / 200000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry94C_hz24 hx hc) (lowGeometry94C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (1032686046946283079 / 1000000000000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry94C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B 1 (53322023577877039 / 50000000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry94C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (197 / 400) (105151030495573521 / 200000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry94C_hz2 hx hc) (lowGeometry94C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (197 / 400) (27244885385274203 / 50000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry94C_hz33 hx hc) (lowGeometry94C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (197 / 400) (27244885385274203 / 50000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry94C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry94C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (967313953053716921 / 1000000000000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry94C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (935696283772408463 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry94C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (3600237654358681 / 7812500000000000) (493 / 1000) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry94C_hz2 hx hc) (lowGeometry94C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (441687864530294713 / 1000000000000000000) (493 / 1000) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry94C_hz38 hx hc) (lowGeometry94C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry94C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (507 / 1000) (203 / 400) θ) : B (441687864530294713 / 1000000000000000000) (493 / 1000) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry94C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry94C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (507 / 1000) (203 / 400) θ) :
    OverlapGuard n θ lowCoreWindow (103690711 / 250000000) (291054753 / 500000000) ∧ radiusMinus n θ lowCoreWindow ≤ (6392577 / 100000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry94C_hz12 hx hc).2
  have hrp := (lowGeometry94C_hz16 hx hc).2
  have hbn := (lowGeometry94C_hz21 hx hc).2
  have hlo := (lowGeometry94C_hz40 hx hc).1
  have hhi := (lowGeometry94C_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]

theorem lowGeometry95W_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (203 / 400) (127 / 250) θ := hc

theorem lowGeometry95W_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry95W_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (123 / 250) (197 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry95W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (24969 / 100000) (25019 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry95W_hz0 hx hc) (lowGeometry95W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (25019 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry95W_hz3 hx hc) (lowGeometry95W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (5592293804871129 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry95W_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (16776881414613387 / 250000000000000000) ((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint (12 : ℝ)) (lowGeometry95W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (203 / 200) (127 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry95W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (1 / 400) ((20 : ℝ) * x) := bmul (bpoint (20 : ℝ)) (lowGeometry95W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (1 / 20) (√((20 : ℝ) * x)) := bsqrt (lowGeometry95W_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (127 / 2500) (((2 : ℝ) * θ) * (√((20 : ℝ) * x))) := bmul (lowGeometry95W_hz7 hx hc) (lowGeometry95W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (29476881414613387 / 250000000000000000) (((12 : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√((20 : ℝ) * x)))) := badd (lowGeometry95W_hz6 hx hc) (lowGeometry95W_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (29476881414613387 / 250000000000000000) (nrm x θ lowWideWindow) := by
    convert (lowGeometry95W_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowWideWindow] <;> ring

theorem lowGeometry95W_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (203 / 10) (508 / 25) (((2 : ℝ) * θ) * (20 : ℝ)) := bmul (lowGeometry95W_hz7 hx hc) (bpoint (20 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (127 / 50000) ((((2 : ℝ) * θ) * (20 : ℝ)) * x) := bmul (lowGeometry95W_hz13 hx hc) (lowGeometry95W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (30111881414613387 / 250000000000000000) ((nrm x θ lowWideWindow) + ((((2 : ℝ) * θ) * (20 : ℝ)) * x)) := badd (lowGeometry95W_hz12 hx hc) (lowGeometry95W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (30111881414613387 / 250000000000000000) (nrp x θ lowWideWindow) := by
    convert (lowGeometry95W_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowWideWindow] <;> ring

theorem lowGeometry95W_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (127 / 2000000) (θ * x) := bmul (lowGeometry95W_hz0 hx hc) (lowGeometry95W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (129065040650407 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry95W_hz17 hx hc) (lowGeometry95W_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (11360679585764533 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry95W_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (34082038757293599 / 500000000000000000) ((6 : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint (6 : ℝ)) (lowGeometry95W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (34082038757293599 / 500000000000000000) (nbp x θ lowWideWindow) := by
    convert (lowGeometry95W_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowWideWindow] <;> ring

theorem lowGeometry95W_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (203 / 50) (508 / 125) (θ * (8 : ℝ)) := bmul (lowGeometry95W_hz0 hx hc) (bpoint (8 : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry95W_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (45436901302795729 / 1000000000000000000) ((θ * (8 : ℝ)) * (√x)) := bmul (lowGeometry95W_hz22 hx hc) (lowGeometry95W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (1 / 10) ((2 : ℝ) * (√((20 : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry95W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (11 / 10) ((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry95W_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (1 / 200) ((40 : ℝ) * x) := bmul (bpoint (40 : ℝ)) (lowGeometry95W_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (221 / 200) (((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)) := badd (lowGeometry95W_hz26 hx hc) (lowGeometry95W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (210237960416286383 / 200000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))) := bsqrt (lowGeometry95W_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (47762807287679399 / 1000000000000000000) (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x)))) := bmul (lowGeometry95W_hz24 hx hc) (lowGeometry95W_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (534082038757293599 / 500000000000000000) ((1 : ℝ) + (nbp x θ lowWideWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry95W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (1140974496492589049 / 1000000000000000000) (((1 : ℝ) + (nbp x θ lowWideWindow))^2) := bsq (lowGeometry95W_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (123 / 250) (561929939522600107 / 1000000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry95W_hz2 hx hc) (lowGeometry95W_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (123 / 250) (304846373405139753 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowWideWindow))^2)) + (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := badd (lowGeometry95W_hz33 hx hc) (lowGeometry95W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (123 / 250) (304846373405139753 / 500000000000000000) (nov x θ lowWideWindow 1) := by
    convert (lowGeometry95W_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry95W_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (465917961242706401 / 500000000000000000) 1 ((1 : ℝ) - (nbp x θ lowWideWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry95W_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (3391867915758751 / 3906250000000000) 1 (((1 : ℝ) - (nbp x θ lowWideWindow))^2) := bsq (lowGeometry95W_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (85442509545129241 / 200000000000000000) (197 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) := bmul (lowGeometry95W_hz2 hx hc) (lowGeometry95W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (189724870218983403 / 500000000000000000) (197 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowWideWindow))^2)) - (((θ * (8 : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√((20 : ℝ) * x)))) + ((40 : ℝ) * x))))) := bsub (lowGeometry95W_hz38 hx hc) (lowGeometry95W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95W_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (189724870218983403 / 500000000000000000) (197 / 400) (nov x θ lowWideWindow (-1)) := by
    convert (lowGeometry95W_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowWideWindow] <;> ring

theorem lowGeometry95W {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (203 / 400) (127 / 250) θ) :
    OverlapGuard n θ lowWideWindow (33865909 / 100000000) (13823783 / 20000000) ∧ radiusMinus n θ lowWideWindow ≤ (58953763 / 500000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry95W_hz12 hx hc).2
  have hrp := (lowGeometry95W_hz16 hx hc).2
  have hbn := (lowGeometry95W_hz21 hx hc).2
  have hlo := (lowGeometry95W_hz40 hx hc).1
  have hhi := (lowGeometry95W_hz35 hx hc).2
  rw [← norm_radiusMinus] at hrm
  rw [← norm_radiusPlus] at hrp
  rw [← norm_planeRatio] at hbn
  rw [← norm_overlap hn0] at hlo hhi
  refine ⟨⟨le_trans (by norm_num) hc.1, lt_of_le_of_lt hc.2 (by norm_num),
    lt_of_le_of_lt hbn (by norm_num), lt_of_le_of_lt hrm (by norm_num),
    by norm_num, ?_, ?_⟩,hrm.trans (by norm_num)⟩
  · nlinarith only [hrp,hlo]
  · nlinarith only [hhi,hrm]
theorem lowGeometry95C_hz0 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (203 / 400) (127 / 250) θ := hc

theorem lowGeometry95C_hz1 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (1 / 8000) x := hx

theorem lowGeometry95C_hz2 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (123 / 250) (197 / 400) ((1 : ℝ) - θ) := bsub (bpoint (1 : ℝ)) (lowGeometry95C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz3 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (24969 / 100000) (25019 / 100000) (θ * ((1 : ℝ) - θ)) := bmul (lowGeometry95C_hz0 hx hc) (lowGeometry95C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz4 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (25019 / 800000000) ((θ * ((1 : ℝ) - θ)) * x) := bmul (lowGeometry95C_hz3 hx hc) (lowGeometry95C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz5 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (5592293804871129 / 1000000000000000000) (√((θ * ((1 : ℝ) - θ)) * x)) := bsqrt (lowGeometry95C_hz4 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz6 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (4026451539507213 / 125000000000000000) (((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) := bmul (bpoint ((144 / 25) : ℝ)) (lowGeometry95C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz7 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (203 / 200) (127 / 125) ((2 : ℝ) * θ) := bmul (bpoint (2 : ℝ)) (lowGeometry95C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz8 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (781 / 800000) (((781 / 100) : ℝ) * x) := bmul (bpoint ((781 / 100) : ℝ)) (lowGeometry95C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz9 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (7811249899983997 / 250000000000000000) (√(((781 / 100) : ℝ) * x)) := bsqrt (lowGeometry95C_hz8 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz10 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (7936229898383741 / 250000000000000000) (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x))) := bmul (lowGeometry95C_hz7 hx hc) (lowGeometry95C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz11 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (15989132977398167 / 250000000000000000) ((((144 / 25) : ℝ) * (√((θ * ((1 : ℝ) - θ)) * x))) + (((2 : ℝ) * θ) * (√(((781 / 100) : ℝ) * x)))) := badd (lowGeometry95C_hz6 hx hc) (lowGeometry95C_hz10 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz12 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (15989132977398167 / 250000000000000000) (nrm x θ lowCoreWindow) := by
    convert (lowGeometry95C_hz11 hx hc) using 1 <;>
      norm_num [nrm,lowCoreWindow] <;> ring

theorem lowGeometry95C_hz13 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (158543 / 20000) (99187 / 12500) (((2 : ℝ) * θ) * ((781 / 100) : ℝ)) := bmul (lowGeometry95C_hz7 hx hc) (bpoint ((781 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz14 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (99187 / 100000000) ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x) := bmul (lowGeometry95C_hz13 hx hc) (lowGeometry95C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz15 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (16237100477398167 / 250000000000000000) ((nrm x θ lowCoreWindow) + ((((2 : ℝ) * θ) * ((781 / 100) : ℝ)) * x)) := badd (lowGeometry95C_hz12 hx hc) (lowGeometry95C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz16 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (16237100477398167 / 250000000000000000) (nrp x θ lowCoreWindow) := by
    convert (lowGeometry95C_hz15 hx hc) using 1 <;>
      norm_num [nrp,lowCoreWindow] <;> ring

theorem lowGeometry95C_hz17 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (127 / 2000000) (θ * x) := bmul (lowGeometry95C_hz0 hx hc) (lowGeometry95C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz18 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (129065040650407 / 1000000000000000000) ((θ * x) / ((1 : ℝ) - θ)) := bdiv (lowGeometry95C_hz17 hx hc) (lowGeometry95C_hz2 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz19 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (11360679585764533 / 1000000000000000000) (√((θ * x) / ((1 : ℝ) - θ))) := bsqrt (lowGeometry95C_hz18 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz20 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (127807645339851 / 3906250000000000) (((72 / 25) : ℝ) * (√((θ * x) / ((1 : ℝ) - θ)))) := bmul (bpoint ((72 / 25) : ℝ)) (lowGeometry95C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz21 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (127807645339851 / 3906250000000000) (nbp x θ lowCoreWindow) := by
    convert (lowGeometry95C_hz20 hx hc) using 1 <;>
      norm_num [nbp,lowCoreWindow] <;> ring

theorem lowGeometry95C_hz22 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (66381 / 40000) (41529 / 25000) (θ * ((327 / 100) : ℝ)) := bmul (lowGeometry95C_hz0 hx hc) (bpoint ((327 / 100) : ℝ)) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz23 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGeometry95C_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz24 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (3714466681503551 / 200000000000000000) ((θ * ((327 / 100) : ℝ)) * (√x)) := bmul (lowGeometry95C_hz22 hx hc) (lowGeometry95C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz25 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (7811249899983997 / 125000000000000000) ((2 : ℝ) * (√(((781 / 100) : ℝ) * x))) := bmul (bpoint (2 : ℝ)) (lowGeometry95C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz26 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (132811249899983997 / 125000000000000000) ((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) := badd (bpoint (1 : ℝ)) (lowGeometry95C_hz25 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz27 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (781 / 400000) (((781 / 50) : ℝ) * x) := bmul (bpoint ((781 / 50) : ℝ)) (lowGeometry95C_hz1 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz28 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (133055312399983997 / 125000000000000000) (((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)) := badd (lowGeometry95C_hz26 hx hc) (lowGeometry95C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz29 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (1031718226649055559 / 1000000000000000000) (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))) := bsqrt (lowGeometry95C_hz28 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz30 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 0 (1916141488793923 / 100000000000000000) (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x)))) := bmul (lowGeometry95C_hz24 hx hc) (lowGeometry95C_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz31 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (4034057645339851 / 3906250000000000) ((1 : ℝ) + (nbp x θ lowCoreWindow)) := badd (bpoint (1 : ℝ)) (lowGeometry95C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz32 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B 1 (66656751967948403 / 62500000000000000) (((1 : ℝ) + (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry95C_hz31 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz33 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (123 / 250) (65656900688429177 / 125000000000000000) (((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry95C_hz2 hx hc) (lowGeometry95C_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz34 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (123 / 250) (272208310197686323 / 500000000000000000) ((((1 : ℝ) - θ) * (((1 : ℝ) + (nbp x θ lowCoreWindow))^2)) + (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := badd (lowGeometry95C_hz33 hx hc) (lowGeometry95C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz35 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (123 / 250) (272208310197686323 / 500000000000000000) (nov x θ lowCoreWindow 1) := by
    convert (lowGeometry95C_hz34 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry95C_hz36 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (3778442354660149 / 3906250000000000) 1 ((1 : ℝ) - (nbp x θ lowCoreWindow)) := bsub (bpoint (1 : ℝ)) (lowGeometry95C_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz37 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (935633002659167023 / 1000000000000000000) 1 (((1 : ℝ) - (nbp x θ lowCoreWindow))^2) := bsq (lowGeometry95C_hz36 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz38 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (18413257492332407 / 40000000000000000) (197 / 400) (((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) := bmul (lowGeometry95C_hz2 hx hc) (lowGeometry95C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz39 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (88234004484074189 / 200000000000000000) (197 / 400) ((((1 : ℝ) - θ) * (((1 : ℝ) - (nbp x θ lowCoreWindow))^2)) - (((θ * ((327 / 100) : ℝ)) * (√x)) * (√(((1 : ℝ) + ((2 : ℝ) * (√(((781 / 100) : ℝ) * x)))) + (((781 / 50) : ℝ) * x))))) := bsub (lowGeometry95C_hz38 hx hc) (lowGeometry95C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGeometry95C_hz40 {x θ : ℝ} (hx : B 0 (1/8000) x) (hc : B (203 / 400) (127 / 250) θ) : B (88234004484074189 / 200000000000000000) (197 / 400) (nov x θ lowCoreWindow (-1)) := by
    convert (lowGeometry95C_hz39 hx hc) using 1 <;>
      norm_num [nov,ngp,lowCoreWindow] <;> ring

theorem lowGeometry95C {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hc : B (203 / 400) (127 / 250) θ) :
    OverlapGuard n θ lowCoreWindow (414264223 / 1000000000) (581614679 / 1000000000) ∧ radiusMinus n θ lowCoreWindow ≤ (15989133 / 250000000) := by
  have hn0 : 0 < n := by omega
  have hx := lowInvDimension hn
  have hrm := (lowGeometry95C_hz12 hx hc).2
  have hrp := (lowGeometry95C_hz16 hx hc).2
  have hbn := (lowGeometry95C_hz21 hx hc).2
  have hlo := (lowGeometry95C_hz40 hx hc).1
  have hhi := (lowGeometry95C_hz35 hx hc).2
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
