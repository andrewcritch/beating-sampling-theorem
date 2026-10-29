import BstLean.Part228Cancellation
import BstLean.Part197Exp

/-! Checked exponential prices for the latitude certificate. -/
namespace BstLean.Part228
open Real

theorem exp_neg_nat_bound (k : ℕ) : exp (-(k : ℝ)) ≤ (36788/100000 : ℝ)^k := by
  have h : exp (-1) ≤ (36788/100000 : ℝ) := by
    have := exp_neg_one_lt_d9
    norm_num at this ⊢
    linarith
  have he : exp (-(k : ℝ)) = exp (-1)^k := by
    rw [← exp_nat_mul]
    congr 1
    ring
  rw [he]
  exact pow_le_pow_left₀ (exp_pos _).le h k

theorem exp_neg_seven_tenths : exp (-(7/10 : ℝ)) ≤ 1/2 := by
  have h := (BstLean.Part197.exp_bounds (N := 8) (x := -(7/10)) (b := 7/10)
    (by norm_num) (by norm_num) (by norm_num)).2
  norm_num [BstLean.Part197.expSum, BstLean.Part197.expError,
    Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_neg_377_tenths : exp (-(377/10 : ℝ)) ≤ 43/10^18 := by
  have he : -(377/10 : ℝ) = -((37 : ℕ) : ℝ) + -(7/10) := by norm_num
  rw [he, exp_add]
  calc _ ≤ (36788/100000 : ℝ)^37 * (1/2) :=
      mul_le_mul (exp_neg_nat_bound 37) exp_neg_seven_tenths
        (exp_pos _).le (by positivity)
    _ ≤ _ := by norm_num

/-- This cap is a consequence of the analytic prices, not the definition of the root. -/
theorem certified_exponent_root_lt :
    √(2*(exp (-(100 : ℝ)) + exp (-(377/10 : ℝ)) + exp (-(41 : ℝ)))) < 1/10^8 := by
  have h100 := exp_neg_nat_bound 100
  have h41 := exp_neg_nat_bound 41
  have h1 : exp (-(100 : ℝ)) ≤ 1/10^40 := h100.trans (by norm_num)
  have h2 : exp (-(41 : ℝ)) ≤ 2/10^18 := h41.trans (by norm_num)
  apply (sqrt_lt' (by norm_num : (0 : ℝ) < 1/10^8)).mpr
  nlinarith [exp_neg_377_tenths]

end BstLean.Part228
