import BstLean.Part235Covariance

/-! Part 235: exact rational enclosures for the joint covariance exceptional term. -/
namespace BstLean.Part235
open Real BstLean.Part199

/-- This bounds the scalar paper tail value. It does not prove the sharp TI event. -/
theorem paper_delta_bound : 50 * exp (-46) ≤ (6 / 10 ^ 19 : ℝ) := by
  have h := BstLean.Part182.exp_neg_nat_le 46
  norm_num at h
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 50)).trans
    (by norm_num)

theorem wide_outside_bound : outsideBound exampleWide ≤ (35 / 10 ^ 9 : ℝ) := by
  have h18 := BstLean.Part182.exp_neg_nat_le 18
  have h20 := BstLean.Part182.exp_neg_nat_le 20
  norm_num at h18 h20
  unfold outsideBound exampleWide
  norm_num
  exact (add_le_add (mul_le_mul_of_nonneg_left h18 (by norm_num))
    (mul_le_mul_of_nonneg_left h20 (by norm_num))).trans (by norm_num)

theorem core_pair_bound : pairRowBound exampleCore ≤ (121 / 10 ^ 4 : ℝ) := by
  have h5 := BstLean.Part182.exp_neg_nat_le 5
  have hl := Real.add_one_le_exp (3 / 25 : ℝ)
  have he : exp (-(3 / 25 : ℝ)) ≤ (25 / 28 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 28 / 25)
      (by linarith only [hl])).trans (by norm_num)
  unfold pairRowBound exampleCore
  norm_num
  rw [show -(128 / 25 : ℝ) = -5 + -(3 / 25) by norm_num, Real.exp_add]
  have hm := mul_le_mul h5 he (Real.exp_nonneg _) (by positivity)
  norm_num at hm
  exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)).trans (by norm_num)

theorem core_outside_bound : outsideBound exampleCore ≤ (409 / 10 ^ 4 : ℝ) := by
  have h3 := BstLean.Part182.exp_neg_nat_le 3
  have h7 := BstLean.Part182.exp_neg_nat_le 7
  have hhalf := BstLean.Part182.exp_neg_half_le
  have hl := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 23 / 25) 6
  norm_num [Finset.sum_range_succ] at hl
  have he : exp (-(23 / 25 : ℝ)) ≤ (292968750 / 734860367 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_div_of_nonneg_left (by norm_num)
      (by norm_num : (0 : ℝ) < 734860367 / 292968750) hl).trans
    norm_num
  have hm3 := mul_le_mul h3 he (Real.exp_nonneg _) (by positivity)
  have hm7 := mul_le_mul h7 hhalf (Real.exp_nonneg _) (by positivity)
  unfold outsideBound exampleCore
  norm_num
  rw [show -(98 / 25 : ℝ) = -3 + -(23 / 25) by norm_num, Real.exp_add,
    show -(15 / 2 : ℝ) = -7 + -(1 / 2) by norm_num, Real.exp_add]
  exact (add_le_add (mul_le_mul_of_nonneg_left hm3 (by norm_num))
    (mul_le_mul_of_nonneg_left hm7 (by norm_num))).trans (by norm_num)

theorem paper_badmass_bound :
    (50 * exp (-46)) / (1 / 4000) ≤ (24 / 10 ^ 16 : ℝ) := by
  have h := mul_le_mul_of_nonneg_left paper_delta_bound
    (by norm_num : (0 : ℝ) ≤ 4000)
  norm_num at h ⊢
  linarith only [h]

/-- The single joint bad mass gives a checked exceptional factor below .001028. -/
theorem joint_exceptional_bound {b : ℝ} (hb : b ≤ 24 / 10 ^ 16) :
    jointExceptionalFactor exampleWide b ≤ (1028 / 10 ^ 6 : ℝ) := by
  have hp : pairRowBound exampleWide ≤ (26 / 10 ^ 15 : ℝ) := by
    simpa only [pairRowBound, exampleWide] using BstLean.Part182.two_exp_neg32
  have hq : √(√(pairRowBound exampleWide + b)) ≤ (420 / 10 ^ 6 : ℝ) := by
    apply BstLean.Part182.sqrt_sqrt_le_of (by norm_num)
    linarith only [hp, hb]
  have ho : √(outsideBound exampleWide) ≤ (188 / 10 ^ 6 : ℝ) := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    linarith only [wide_outside_bound]
  unfold jointExceptionalFactor
  linarith only [hq, ho]

end BstLean.Part235
