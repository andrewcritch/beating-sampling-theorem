import BstLean.Part197Exp
import BstLean.Part197Log
import BstLean.Part285IntervalTools

/-! Short Taylor bounds for exact rational END certificates. -/
namespace BstLean.Part293
open Real BstLean.Part197

noncomputable def expApprox16 (x : ℝ) : ℝ :=
  1 + x * (1 + x * (1/2 + x * (1/6 + x * (1/24 + x * (1/120 +
    x * (1/720 + x * (1/5040 + x * (1/40320 + x * (1/362880 +
    x * (1/3628800 + x * (1/39916800 + x * (1/479001600 +
    x * (1/6227020800 + x * (1/87178291200 + x * (1/1307674368000)))))))))))))))

theorem expApprox16_eq (x : ℝ) : expApprox16 x = expSum 16 x := by
  norm_num [expApprox16, expSum, Finset.sum_range_succ, Nat.factorial]
  ring

theorem exp_enclose {x l u : ℝ} (hx : |x| ≤ 1)
    (hl : l ≤ expApprox16 x - 1 / 10 ^ 12)
    (hu : expApprox16 x + 1 / 10 ^ 12 ≤ u) : l ≤ exp x ∧ exp x ≤ u := by
  have h := exp_bounds (N := 16) (b := 1) (by norm_num) hx le_rfl
  have he : expError 16 1 ≤ (1 : ℝ) / 10 ^ 12 := by
    norm_num [expError, Nat.factorial]
  rw [← expApprox16_eq] at h
  constructor <;> linarith [h.1, h.2]

noncomputable def logApprox10 (x : ℝ) : ℝ :=
  x * (1 - x * (1/2 - x * (1/3 - x * (1/4 - x * (1/5 -
    x * (1/6 - x * (1/7 - x * (1/8 - x * (1/9 - x * (1/10))))))))))

theorem logApprox10_eq (x : ℝ) : logApprox10 x = logOneAddSum 10 x := by
  norm_num [logApprox10, logOneAddSum, Finset.sum_range_succ]
  ring

theorem log_one_add_enclose {x l u : ℝ} (hx : |x| ≤ 1 / 16)
    (hl : l ≤ logApprox10 x - 1 / 10 ^ 12)
    (hu : logApprox10 x + 1 / 10 ^ 12 ≤ u) : l ≤ log (1 + x) ∧ log (1 + x) ≤ u := by
  have h := log_one_add_remainder (by linarith : |x| < 1) 10
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 11
  have hd : 0 < 1 - |x| := by linarith
  have he : |x| ^ 11 / (1 - |x|) ≤ (1 : ℝ) / 10 ^ 12 := by
    apply (div_le_iff₀ hd).mpr
    norm_num at hp
    linarith
  rw [← logApprox10_eq] at h
  have hh := abs_le.mp (h.trans he)
  constructor <;> linarith [hh.1, hh.2]

theorem exp_scaled_upper {x v u : ℝ} (hv : exp (x / 64) ≤ v) (hu : v ^ 64 ≤ u) :
    exp x ≤ u := by
  rw [exp_range_reduction x (show 0 < (64 : ℕ) by norm_num)]
  exact (pow_le_pow_left₀ (exp_pos _).le hv 64).trans hu

theorem exp_probe : (135334 / 10 ^ 6 : ℝ) ≤ exp (-2) ∧ exp (-2) ≤ 135336 / 10 ^ 6 := by
  have h : (969233234475 / 10 ^ 12 : ℝ) ≤ exp (-(2 : ℝ) / 64) ∧
      exp (-(2 : ℝ) / 64) ≤ 969233234478 / 10 ^ 12 := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  rw [exp_range_reduction (-2) (show 0 < (64 : ℕ) by norm_num)]
  constructor
  · have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 969233234475 / 10 ^ 12) h.1 64
    have hl : (135334 / 10 ^ 6 : ℝ) ≤ (969233234475 / 10 ^ 12) ^ 64 := by norm_num
    exact hl.trans hp
  · exact (pow_le_pow_left₀ (exp_pos _).le h.2 64).trans (by norm_num)

end BstLean.Part293

/-- info: 'BstLean.Part293.exp_enclose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.exp_enclose
/-- info: 'BstLean.Part293.log_one_add_enclose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.log_one_add_enclose
