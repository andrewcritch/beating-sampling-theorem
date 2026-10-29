import BstLean.Part253Exp
namespace BstLean.Part269.Tails
open Real

theorem exp_negative_sixteen_bound {a E B : ℝ} (ha : 0 ≤ a) (hE : 0 < E)
    (hSum : E ≤ ∑ i ∈ Finset.range 12, (a / 16) ^ i / i.factorial)
    (hB : (E ^ 16)⁻¹ ≤ B) : exp (-a) ≤ B := by
  have h := hSum.trans (sum_le_exp_of_nonneg (div_nonneg ha (by norm_num)) 12)
  have he : exp a = exp (a / 16) ^ 16 := by
    convert exp_nat_mul (a / 16) 16 using 1 <;> ring
  have hp : E ^ 16 ≤ exp a := by
    rw [he]
    exact pow_le_pow_left₀ hE.le h 16
  rw [exp_neg]
  exact ((inv_le_inv₀ (exp_pos _) (pow_pos hE 16)).mpr hp).trans hB

theorem exp_minus_17_1_upper : exp (-17.1 : ℝ) ≤ 3.7460E-8 := by
  apply exp_negative_sixteen_bound (E := (2.911737547244 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_17_2_upper : exp (-17.2 : ℝ) ≤ 3.3895E-8 := by
  apply exp_negative_sixteen_bound (E := (2.929992895116 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_17_3_upper : exp (-17.3 : ℝ) ≤ 3.0670E-8 := by
  apply exp_negative_sixteen_bound (E := (2.948362696183 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_17_4_upper : exp (-17.4 : ℝ) ≤ 2.7751E-8 := by
  apply exp_negative_sixteen_bound (E := (2.966847668017 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_17_5_upper : exp (-17.5 : ℝ) ≤ 2.5110E-8 := by
  apply exp_negative_sixteen_bound (E := (2.985448532688 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_17_6_upper : exp (-17.6 : ℝ) ≤ 2.2721E-8 := by
  apply exp_negative_sixteen_bound (E := (3.004166016793 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_17_7_upper : exp (-17.7 : ℝ) ≤ 2.0559E-8 := by
  apply exp_negative_sixteen_bound (E := (3.023000851484 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_17_8_upper : exp (-17.8 : ℝ) ≤ 1.8602E-8 := by
  apply exp_negative_sixteen_bound (E := (3.041953772497 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_17_9_upper : exp (-17.9 : ℝ) ≤ 1.6832E-8 := by
  apply exp_negative_sixteen_bound (E := (3.061025520183 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_18_0_upper : exp (-18.0 : ℝ) ≤ 1.5230E-8 := by
  apply exp_negative_sixteen_bound (E := (3.080216839530 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_18_1_upper : exp (-18.1 : ℝ) ≤ 1.3781E-8 := by
  apply exp_negative_sixteen_bound (E := (3.099528480201 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_18_2_upper : exp (-18.2 : ℝ) ≤ 1.2470E-8 := by
  apply exp_negative_sixteen_bound (E := (3.118961196557 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_18_3_upper : exp (-18.3 : ℝ) ≤ 1.1283E-8 := by
  apply exp_negative_sixteen_bound (E := (3.138515747688 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_18_4_upper : exp (-18.4 : ℝ) ≤ 1.0209E-8 := by
  apply exp_negative_sixteen_bound (E := (3.158192897444 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

end BstLean.Part269.Tails
