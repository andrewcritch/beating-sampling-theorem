import BstLean.Part293Ledger
import BstLean.Part253Exp

/-! The elementary event charges hold on the entire low band. -/
namespace BstLean.Part293
open Real

theorem angle_payment {n : ℕ} (hn : 8000 ≤ n) :
    exp (-(45 / 10000 * (n : ℝ))) + exp (-12) ≤ angleCharge := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have h36 := BstLean.Part253.exp_negative_bound 36
    (by norm_num : ((2.71828 : ℝ) ^ 36)⁻¹ ≤ 1 / 10 ^ 15)
  have h := (exp_le_exp.mpr (show -(45 / 10000 * (n : ℝ)) ≤ -36 by linarith)).trans h36
  have h12 := BstLean.Part253.exp_minus_twelve_upper
  norm_num [angleCharge] at *
  linarith

theorem latitude_payment : 1 / 10 ^ 4 + exp (-12 : ℝ) ≤ latitudeCharge := by
  have h := BstLean.Part253.exp_minus_twelve_upper
  norm_num [latitudeCharge] at *
  linarith

theorem source_payment {n : ℕ} (hn : 8000 ≤ n) :
    exp (-(n : ℝ) / 2) + 3445 / (n : ℝ) ^ 2 + 15 * exp (-12) + 0.00038 ≤ sourceCharge := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have h25 := BstLean.Part253.exp_negative_bound 25
    (by norm_num : ((2.71828 : ℝ) ^ 25)⁻¹ ≤ 1 / 10 ^ 9)
  have h := (exp_le_exp.mpr (show -(n : ℝ) / 2 ≤ -25 by linarith)).trans h25
  have h12 := BstLean.Part253.exp_negative_bound 12
    (by norm_num : ((2.71828 : ℝ) ^ 12)⁻¹ ≤ 61443 / 10 ^ 10)
  have hr : (3445 : ℝ) / (n : ℝ) ^ 2 ≤ 3445 / 8000 ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact pow_le_pow_left₀ (by norm_num) hnR 2
  norm_num [sourceCharge] at *
  linarith

end BstLean.Part293

/-- info: 'BstLean.Part293.angle_payment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.angle_payment
