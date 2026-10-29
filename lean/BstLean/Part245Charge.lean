import BstLean.Part244TI

/-! Part 245: the sharp block charge exceeds the old bad-mass cutoff. -/
namespace BstLean.Part245
open Real BstLean.Part130

noncomputable def maskSlack (n : ℕ) : ℝ := √(46 / (2 * (mA n : ℝ)))

theorem maskSlack_nonneg (n : ℕ) : 0 ≤ maskSlack n := Real.sqrt_nonneg _

theorem maskSlack_exponent {n : ℕ} (hn : 0 < n) :
    2 * maskSlack n ^ 2 * (mA n : ℝ) = 46 := by
  have hm : (0 : ℝ) < mA n := by exact_mod_cast (pow_pos hn 2)
  unfold maskSlack
  rw [Real.sq_sqrt (by positivity)]
  field_simp

theorem sharp_charge_eq {n : ℕ} (hn : 0 < n) :
    53 * exp (-46) + 12 * exp (-2 * maskSlack n ^ 2 * (mA n : ℝ)) =
      65 * exp (-46) := by
  rw [show -2 * maskSlack n ^ 2 * (mA n : ℝ) = -46 by
    linarith [maskSlack_exponent hn]]
  ring

theorem exp_neg46_lower : (1053 / 10 ^ 23 : ℝ) ≤ exp (-46) := by
  have he : exp (46 : ℝ) ≤ (2718281829 / 10 ^ 9 : ℝ) ^ 46 := by
    have hid : exp (46 : ℝ) = exp 1 ^ 46 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hid]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) (by linarith [Real.exp_one_lt_d9]) 46
  rw [Real.exp_neg]
  exact (show (1053 / 10 ^ 23 : ℝ) ≤ ((2718281829 / 10 ^ 9 : ℝ) ^ 46)⁻¹ by
    norm_num).trans (inv_anti₀ (Real.exp_pos _) he)

/-- The current sharp charge with payment 1/4000 misses the old cutoff. -/
theorem sharp_badmass_exceeds {n : ℕ} (hn : 0 < n) :
    (24 / 10 ^ 16 : ℝ) <
      (53 * exp (-46) + 12 * exp (-2 * maskSlack n ^ 2 * (mA n : ℝ))) /
        (1 / 4000) := by
  rw [sharp_charge_eq hn]
  have h := exp_neg46_lower
  linarith

/-- A larger payment fits the same scalar cutoff. This is not a total-ledger bound. -/
theorem sharp_badmass_3400 {n : ℕ} (hn : 0 < n) :
    (53 * exp (-46) + 12 * exp (-2 * maskSlack n ^ 2 * (mA n : ℝ))) /
      (1 / 3400) ≤ (24 / 10 ^ 16 : ℝ) := by
  rw [sharp_charge_eq hn]
  have h := BstLean.Part182.exp_neg_nat_le 46
  norm_num at h
  have hb : exp (-46) ≤ (106 / 10 ^ 22 : ℝ) := h.trans (by norm_num)
  linarith

end BstLean.Part245
