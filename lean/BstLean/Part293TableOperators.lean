import BstLean.Part292Operators

/-! The paid operator sizes give the fixed product cap independently of the table charge. -/
namespace BstLean.Part293
open Real BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170 BstLean.Part292

theorem second_operator_square_low {n : ℕ} (hn : 8000 ≤ n) :
    lowSecondOperator n ^ 2 ≤ (2.83 : ℝ) ^ 2 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  unfold lowSecondOperator
  rw [mul_pow, sq_sqrt (show 0 ≤ tA n by unfold tA; positivity)]
  unfold tA mA
  push_cast
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hn0 2)]
  nlinarith [mul_le_mul_of_nonneg_right hnR hn0.le]

theorem operator_product_square_low {n : ℕ} (hn : 8000 ≤ n) :
    (lowSecondOperator n * lowOperator n) ^ 2 ≤ 16.411 * (n : ℝ) := by
  rw [mul_pow]
  apply (mul_le_mul (second_operator_square_low hn) (lowOperator_square hn)
    (sq_nonneg _) (by positivity)).trans
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith

end BstLean.Part293
