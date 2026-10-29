import BstLean.Part252NormalizedVariance
import BstLean.Part252Root
import BstLean.Part212Fields

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12225 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12225) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12225 : ℝ) * (12225 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12225) /
    ((12225 : ℝ) * (12225 - 1 - 2 * q)))

theorem rotation_positive (q : ℕ) : 0 < rotationConstant q := by
  have ho : 0 < oddMoment q := by
    unfold oddMoment
    exact Finset.prod_pos (fun j _ => by positivity)
  unfold rotationConstant
  split_ifs
  · norm_num
  · exact mul_pos (by positivity) (Real.rpow_pos_of_pos ho _)

theorem locationMomentBudget_pos {c : Ret 12225} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12225) c a v - lbar (paperDesignP 12225) c a| ^ (2 * q)
      ∂stdGauss (Fin (12225 - 1)) ∂muI 12225 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12225)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12225) c a v - gbar (paperDesignP 12225) c a| ^ (2 * q)
      ∂stdGauss (Fin (12225 - 1)) ∂muI 12225 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12225)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12225) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12225 - 1))).real
      {v | sgA (paperDesignP 12225) c a v < √(2 / (12225 : ℝ) * mixtureFloor)}
      ∂muI 12225 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12225 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12225 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12225) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part252
