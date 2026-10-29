import BstLean.Part253IdealCells0
import BstLean.Part253IdealCells4
import BstLean.Part253Data

/-! The Part219 direction field has a numerical supply under the remaining
centre-energy and operator scalar inputs. -/
namespace BstLean.Part253
open Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part219 BstLean.Part215

theorem ideal_window {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 12225 θ e ≤ 0.230 := by
  by_cases h1 : θ ≤ 0.4744
  · exact idealCell0 ⟨hw.1, h1⟩ he
  by_cases h2 : θ ≤ 0.4816
  · exact idealCell1 ⟨by linarith, h2⟩ he
  by_cases h3 : θ ≤ 0.4888
  · exact idealCell2 ⟨by linarith, h3⟩ he
  by_cases h4 : θ ≤ 0.496
  · exact idealCell3 ⟨by linarith, h4⟩ he
  by_cases h5 : θ ≤ 0.5032
  · exact idealCell4 ⟨by linarith, h5⟩ he
  by_cases h6 : θ ≤ 0.5104
  · exact idealCell5 ⟨by linarith, h6⟩ he
  by_cases h7 : θ ≤ 0.5176
  · exact idealCell6 ⟨by linarith, h7⟩ he
  exact idealCell7 ⟨by linarith, hw.2⟩ he

theorem needed_direction_window {i : Fin 60} (hi : needed i) {θ : ℝ}
    (hm : θ ∈ cell i) : θ ∈ Icc (0.47199 : ℝ) 0.52358 := by
  have hlo := noiseNode_mono hi.1
  have hhi := noiseNode_mono (show i.val + 1 ≤ 53 by have := hi.2; omega)
  have hnlo : (0.47199 : ℝ) ≤ noiseNode 10 := by norm_num [noiseNode]
  have hnhi : noiseNode 53 ≤ (0.52358 : ℝ) := by norm_num [noiseNode]
  exact ⟨hnlo.trans (hlo.trans hm.1), hm.2.trans (hhi.trans hnhi)⟩

theorem direction_budget_le (c : Fin 12225 → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞)
    (hw : BstLean.Part150.thetaC c τ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.1)
    (hop : operatorAllowance c τ eta δ ^ 2 ≤ 1.22) :
    paperDirectionBudget c τ e xi eta δ ≤ directionCap := by
  let θ := BstLean.Part150.thetaC c τ
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hθ1 : θ ≤ 0.52358 := hw.2
  have hR : radiusCoefficient 12225 12 θ ≤ 0.525 :=
    radius_upper 12 hθ hw.2 (by norm_num) (by norm_num)
  have hR0 : 0 ≤ radiusCoefficient 12225 12 θ := by
    unfold radiusCoefficient
    simp only [Nat.cast_ofNat]
    apply div_nonneg hθ
    linarith
  have hRs : √(radiusCoefficient 12225 12 θ / e) ≤ 0.889 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.525 : ℝ) / 0.665 := div_le_div₀ (by norm_num) hR (by norm_num) he
      _ ≤ (0.889 : ℝ) ^ 2 := by norm_num
  have heps := error_epsilon_upper
  have heps0 := BstLean.Part209.meanEpsilon_nonneg 12225 16
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1)
  have hEp0 : 0 ≤ BstLean.Part209.pairEpsilon 12225 16 (1 / 100) :=
    add_nonneg heps0 (BstLean.Part209.fluctuationRoot_nonneg _ _)
  have hroot : (0.88 : ℝ) ≤ (7 / 25000 : ℝ) ^ (1 / 64 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by positivity)
    have hh := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 7 / 25000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh]
    norm_num
  have htransfer : √(operatorAllowance c τ eta δ ^ 2 * xi / ((12225 : ℝ) * e)) ≤
      0.00388 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1.22 : ℝ) * 0.1 / (12225 * 0.665) := by gcongr
      _ ≤ (0.00388 : ℝ) ^ 2 := by norm_num
  have hi := ideal_window hw he
  have hi0 : 0 ≤ paperIdeal 12225 θ e := by
    have hr (j : ℕ) (hj : j ≤ 96) : 0 ≤ radiusCoefficient 12225 j θ := by
      unfold radiusCoefficient
      simp only [Nat.cast_ofNat]
      apply div_nonneg hθ
      have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
      have hp := mul_le_mul (show (2 * j + 2 : ℝ) ≤ 194 by linarith) hθ1 hθ
        (by norm_num : (0 : ℝ) ≤ 194)
      nlinarith
    have hr48 := hr 48 (by norm_num)
    have hr96 := hr 96 (by norm_num)
    have hr4 := hr 4 (by norm_num)
    have hk := kernelSlope_nonneg (1 - θ)
    have hrot := BstLean.Part195.rotationConstant_nonneg 24
    unfold paperIdeal paperAmplitude paperBias
    positivity
  unfold paperDirectionBudget
  simp only [Nat.cast_ofNat]
  change (paperIdeal 12225 θ e + _ + _) ^ 2 ≤ _
  calc
    _ ≤ ((0.230 : ℝ) + 0.0647 * 0.889 / 0.88 + 0.00388) ^ 2 := by gcongr
    _ ≤ directionCap := by norm_num [directionCap]

end BstLean.Part253
