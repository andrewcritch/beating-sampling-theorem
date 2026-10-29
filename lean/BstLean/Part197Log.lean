import BstLean.Part193Interval
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Part 197: logarithm remainders and positive TG domains. -/
namespace BstLean.Part197

open BstLean.Part193

noncomputable def logOneAddSum (N : ℕ) (x : ℝ) : ℝ :=
  -(∑ j ∈ Finset.range N, (-x) ^ (j + 1) / ((j + 1 : ℕ) : ℝ))

theorem log_one_add_remainder {x : ℝ} (hx : |x| < 1) (N : ℕ) :
    |Real.log (1 + x) - logOneAddSum N x| ≤ |x| ^ (N + 1) / (1 - |x|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by simpa using hx) N
  simpa [logOneAddSum, sub_neg_eq_add, add_comm] using h

theorem log_one_add_mem {x : ℝ} {N : ℕ} {P J : Interval} (hx : |x| < 1)
    (hP : P.Mem (logOneAddSum N x))
    (hl : J.lo ≤ P.lo - |x| ^ (N + 1) / (1 - |x|))
    (hu : P.hi + |x| ^ (N + 1) / (1 - |x|) ≤ J.hi) :
    J.Mem (Real.log (1 + x)) := by
  have h := abs_le.mp (log_one_add_remainder hx N)
  constructor <;> linarith [hP.1, hP.2, h.1, h.2]

noncomputable def logRatioSum (N : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range N, x ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)

/-- The odd-power series encloses the exact logarithm for either sign of x. -/
theorem log_ratio_remainder {x : ℝ} (hx : |x| < 1) (N : ℕ) :
    |Real.log ((1 + x) / (1 - x)) - logRatioSum N x| ≤
      2 * (|x| ^ (2 * N + 1) / (1 - x ^ 2)) := by
  have h := Real.sum_range_sub_log_div_le hx N
  have hid : Real.log ((1 + x) / (1 - x)) - logRatioSum N x =
      2 * (1 / 2 * Real.log ((1 + x) / (1 - x)) -
        ∑ j ∈ Finset.range N, x ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)) := by
    unfold logRatioSum
    ring
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

/-- Every positive logarithm argument has a ratio parameter strictly between minus one and one. -/
theorem log_positive_reduction {y : ℝ} (hy : 0 < y) :
    |(y - 1) / (y + 1)| < 1 ∧
      (1 + (y - 1) / (y + 1)) / (1 - (y - 1) / (y + 1)) = y := by
  have hd : 0 < y + 1 := by linarith
  constructor
  · rw [abs_lt]
    constructor
    · rw [lt_div_iff₀ hd]; linarith
    · rw [div_lt_iff₀ hd]; linarith
  · field_simp
    ring

theorem log_positive_remainder {y : ℝ} (hy : 0 < y) (N : ℕ) :
    |Real.log y - logRatioSum N ((y - 1) / (y + 1))| ≤
      2 * (|(y - 1) / (y + 1)| ^ (2 * N + 1) /
        (1 - ((y - 1) / (y + 1)) ^ 2)) := by
  have h := log_positive_reduction hy
  simpa only [h.2] using log_ratio_remainder h.1 N

theorem log_positive_mem {y : ℝ} {N : ℕ} {P J : Interval} (hy : 0 < y)
    (hP : P.Mem (logRatioSum N ((y - 1) / (y + 1))))
    (hl : J.lo ≤ P.lo - 2 * (|(y - 1) / (y + 1)| ^ (2 * N + 1) /
      (1 - ((y - 1) / (y + 1)) ^ 2)))
    (hu : P.hi + 2 * (|(y - 1) / (y + 1)| ^ (2 * N + 1) /
      (1 - ((y - 1) / (y + 1)) ^ 2)) ≤ J.hi) : J.Mem (Real.log y) := by
  have h := abs_le.mp (log_positive_remainder hy N)
  constructor <;> linarith [hP.1, hP.2, h.1, h.2]

noncomputable def tangentConstant (x c : ℝ) : ℝ :=
  (Real.log (1 + x) - x / (1 + x)) / c

theorem tangent_constant_nonneg {x c : ℝ} (hx : -1 < x) (hc : 0 < c) :
    0 ≤ tangentConstant x c := by
  have hy : 0 < 1 + x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hy
  have heq : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  rw [heq] at h
  exact div_nonneg (sub_nonneg.mpr h) hc.le

/-- Both signs of the World transform require the actual positive log argument. -/
theorem tg_world_domain {v Y : ℝ} (h : 0 < 1 + v * Y) :
    -1 < v * Y ∧ 1 + v * Y ≠ 0 ∧ |((1 + v * Y) - 1) / ((1 + v * Y) + 1)| < 1 := by
  exact ⟨by linarith, h.ne', (log_positive_reduction h).1⟩

theorem tg_agent_domain {u : ℝ} (h : -1 < u) :
    0 < 1 + u ∧ 1 + u ≠ 0 := by
  have hp : 0 < 1 + u := by linarith
  exact ⟨hp, hp.ne'⟩

end BstLean.Part197
