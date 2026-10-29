import BstLean.Part213Norm

namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real
noncomputable def statisticsConstant (B : ℝ) : ℝ := (30000 : ℝ) ^ (416 : ℝ)⁻¹ * B

lemma statisticsConstant_pow (B : ℝ) : statisticsConstant B ^ 416 = 30000 * B ^ 416 := by
  have hp : ((30000 : ℝ) ^ (416 : ℝ)⁻¹) ^ (416 : ℕ) = 30000 := by
    simpa using Real.rpow_inv_natCast_pow (x := (30000 : ℝ)) (n := 416)
      (by norm_num) (by norm_num)
  rw [statisticsConstant, mul_pow, hp]

lemma statisticsConstant_pos {B : ℝ} (hB : 0 < B) : 0 < statisticsConstant B := by
  unfold statisticsConstant
  positivity

/-- The exact threshold spends one ten-thousandth on all three statistics. -/
lemma three_statistics_price {B : ℝ} (hB : 0 < B) :
    3 * (B / statisticsConstant B) ^ 416 = 1 / 10000 := by
  rw [div_pow, statisticsConstant_pow]
  field_simp [ne_of_gt hB]
  ring


#print axioms three_statistics_price
end BstLean.Part239
