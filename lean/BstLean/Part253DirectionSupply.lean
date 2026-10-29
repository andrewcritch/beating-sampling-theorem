import BstLean.Part253Direction
import BstLean.Part253Operator
import BstLean.Part253Supply

/-! The actual direction moment uses checked constants and the existing source events. -/
namespace BstLean.Part253
open Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part153 BstLean.Part188
open BstLean.Part169 (paperDesignP)

theorem direction_with_operator (c : Fin 12225 → ℝ) {τ e xi : ℝ} (hτ : 0 < τ)
    (hw : BstLean.Part150.thetaC c τ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.1) :
    BstLean.Part219.paperDirectionBudget c τ e xi 0.006 (ENNReal.ofReal (1 / 20000)) ≤
      directionCap :=
  direction_budget_le c τ e xi 0.006 _ hw he hxi hxi1 (operator_allowance_le c hτ)

theorem direction_on_source_events {c : Ret 12225} {i : Fin 60}
    (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell i)
    (hτ : 0 < (paperDesignP 12225).tau0 c) {xi : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.1)
    (hb : (12225 : ℝ) * 0.665 ≤ normSq ((paperDesignP 12225).bA c.1 c.2.1.1))
    (hfull : normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP 12225).tau0 c) -
      (paperDesignP 12225).bA c.1 c.2.1.1) ≤ xi)
    (herr : c.2.1.1 ∈ BstLean.Part215.sharpErrorEvent c.1.2 ((paperDesignP 12225).tau0 c))
    (hop : c.2.1.1 ∈ BstLean.Part215.operatorEvent c.1.2 ((paperDesignP 12225).tau0 c)
      0.006 (ENNReal.ofReal (1 / 20000))) :
    DirectionMoment (paperDesignP 12225) c directionCap := by
  have hw := needed_direction_window hi hm
  have hq : 1 - BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      Icc (0 : ℝ) (27 / 50) := ⟨by have := hw.2; linarith, by have := hw.1; linarith⟩
  exact BstLean.Part219.directionMoment_mono
    (BstLean.Part219.directionMoment_paper (by norm_num) (paperDesignP 12225) c hτ
      (by norm_num : (0 : ℝ) < 0.665) hxi (by norm_num) hq hb hfull herr hop)
    (direction_with_operator c.1.2 hτ hw le_rfl hxi hxi1)

end BstLean.Part253
