import BstLean.Part252LatMomPacket
import BstLean.Part252EnergyRange

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem rotation_four : rotationConstant 4 ≤ 285 / 100 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem rotation_six : rotationConstant 6 ≤ 35 / 10 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem rotation_twelve : rotationConstant 12 ≤ 48 / 10 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem location_budget_cap {c : Ret 12225} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12225 : ℝ) * (12225 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12225 : ℝ) * (12225 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12225 : ℝ) /
      ((12225 : ℝ) * (12225 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12225 : ℝ) * (12225 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12225 ≤ (2 * (16 / 5) / 12225 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12225} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ 54 / 10 ^ 5 ∧
    locationMomentBudget c 6 ≤ 665 / 10 ^ 6 ∧
    locationMomentBudget c 12 ≤ 91 / 10 ^ 5 := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ 534 / 10 ^ 8 ∧
    residualMomentBudget 6 ≤ 656 / 10 ^ 8 ∧
    residualMomentBudget 12 ≤ 9 / 10 ^ 6 := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12225} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ 357 / 10 ^ 10 ∧ residualVarianceBudget ≤ 3505 / 10 ^ 15 := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12225 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * (534 / 10 ^ 8 : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part252
