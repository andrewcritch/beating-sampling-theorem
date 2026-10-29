import BstLean.Part254Tails
import BstLean.Part146Tail

/-! Rational enclosures of the paper's Gaussian tail values. These bounds do
not replace the exponential tails in Part238's assembly automatically. -/
namespace BstLean.Part254
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part131 BstLean.Part144 BstLean.Part146 BstLean.Part156

noncomputable def gaussianTail (t : ℝ) : ℝ := 2 * (gaussianReal 0 1).real (Ioi t)

theorem normalizing_factor_bounds :
    (398942280 / 10 ^ 9 : ℝ) ≤ (√(2 * π))⁻¹ ∧
    (√(2 * π))⁻¹ ≤ (398942281 / 10 ^ 9 : ℝ) := by
  have hl : (2506628274 / 10 ^ 9 : ℝ) ≤ √(2 * π) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [Real.pi_gt_d20]
  have hu : √(2 * π) ≤ (2506628275 / 10 ^ 9 : ℝ) := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    nlinarith only [Real.pi_lt_d20]
  constructor
  · rw [← one_div]
    exact (by norm_num : (398942280 / 10 ^ 9 : ℝ) ≤ 1 / (2506628275 / 10 ^ 9)).trans
      (one_div_le_one_div_of_le (by positivity) hu)
  · rw [← one_div]
    exact (one_div_le_one_div_of_le (by norm_num) hl).trans (by norm_num)

theorem gaussianTail_enclosure {t lo hi L U : ℝ} (ht : 0 < t) (hlo : 0 ≤ lo)
    (heL : lo ≤ exp (-(t ^ 2 / 2))) (heU : exp (-(t ^ 2 / 2)) ≤ hi)
    (hL : L ≤ 2 * (398942280 / 10 ^ 9 * lo * ((t ^ 3 + 5 * t) / (t ^ 4 + 6 * t ^ 2 + 3))))
    (hU : 2 * (398942281 / 10 ^ 9 * hi * (nP t / (t * eP t))) ≤ U) :
    L ≤ gaussianTail t ∧ gaussianTail t ≤ U := by
  have hpL : (398942280 / 10 ^ 9) * lo ≤ gaussianPDFReal 0 1 t := by
    rw [pdf_eq]
    exact mul_le_mul normalizing_factor_bounds.1 heL hlo (by positivity)
  have hpU : gaussianPDFReal 0 1 t ≤ (398942281 / 10 ^ 9) * hi := by
    rw [pdf_eq]
    exact mul_le_mul normalizing_factor_bounds.2 heU (exp_nonneg _) (by norm_num)
  constructor
  · refine hL.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpL (by positivity)) (by norm_num)).trans ?_)
    exact mul_le_mul_of_nonneg_left (mills4_lower ht) (by norm_num)
  · refine (mul_le_mul_of_nonneg_left (mills9_upper ht) (by norm_num)).trans ?_
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpU
        (div_nonneg (nP_pos t).le (mul_pos ht (eP_pos t)).le))
      (by norm_num : (0 : ℝ) ≤ 2)).trans hU

theorem gaussian_abs_tail_le (t : ℝ) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ gaussianTail t := two_sided_le t

end BstLean.Part254
