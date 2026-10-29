import BstLean.Part249Covariance
import BstLean.Part160Ledger2Gen

/-! Rational enclosures for the exponential tails in the existing covariance
transfer. These tails are Chernoff bounds, not Gaussian tail probabilities. -/
namespace BstLean.Part254
open Real BstLean.Part199 BstLean.Part156

theorem core_pair_upper : pairRowBound exampleCore ≤ (11952045791 / 10 ^ 12 : ℝ) := by
  have h : exp (-(64 / 100 : ℝ)) ≤ 527292424044 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hp := pow_le_pow_left₀ (exp_nonneg _) h 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  norm_num [pairRowBound, exampleCore]
  exact (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)).trans (by norm_num)

theorem core_outside_upper : outsideBound exampleCore ≤ (40788358230 / 10 ^ 12 : ℝ) := by
  have h1 : exp (-(98 / 100 : ℝ)) ≤ 375311098852 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have h2 : exp (-(9375 / 10000 : ℝ)) ≤ 391605626677 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hp1 := pow_le_pow_left₀ (exp_nonneg _) h1 4
  have hp2 := pow_le_pow_left₀ (exp_nonneg _) h2 8
  rw [← Real.exp_nat_mul] at hp1 hp2
  norm_num at hp1 hp2
  norm_num [outsideBound, exampleCore]
  exact (add_le_add (mul_le_mul_of_nonneg_left hp1 (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hp2 (by norm_num : (0 : ℝ) ≤ 2))).trans (by norm_num)

end BstLean.Part254
