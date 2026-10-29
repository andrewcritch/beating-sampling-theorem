import BstLean.Part193Expr
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Part 197: finite exponential sums and proved remainders. -/
namespace BstLean.Part197

open BstLean.Part193

noncomputable def expSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, x ^ j / (j.factorial : ℝ)

noncomputable def expError (N : ℕ) (b : ℝ) : ℝ :=
  b ^ N * (((N : ℝ) + 1) / ((N.factorial : ℝ) * N))

theorem exp_remainder {x b : ℝ} {N : ℕ} (hN : 0 < N)
    (hx : |x| ≤ b) (hb : b ≤ 1) :
    |Real.exp x - expSum N x| ≤ expError N b := by
  have h := Real.exp_bound (hx.trans hb) hN
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx N
  have hc : 0 ≤ ((N : ℝ) + 1) / ((N.factorial : ℝ) * N) := by positivity
  have hm := mul_le_mul_of_nonneg_right hp hc
  simp only [Nat.cast_succ] at h
  exact h.trans hm

theorem exp_bounds {x b : ℝ} {N : ℕ} (hN : 0 < N)
    (hx : |x| ≤ b) (hb : b ≤ 1) :
    expSum N x - expError N b ≤ Real.exp x ∧
      Real.exp x ≤ expSum N x + expError N b := by
  have h := abs_le.mp (exp_remainder hN hx hb)
  constructor <;> linarith

/-- An exact polynomial enclosure and a checked error give an exponential enclosure. -/
theorem exp_mem {x b : ℝ} {N : ℕ} {P J : Interval} (hN : 0 < N)
    (hx : |x| ≤ b) (hb : b ≤ 1) (hP : P.Mem (expSum N x))
    (hl : J.lo ≤ P.lo - expError N b) (hu : P.hi + expError N b ≤ J.hi) :
    J.Mem (Real.exp x) := by
  have h := exp_bounds hN hx hb
  constructor <;> linarith [hP.1, hP.2, h.1, h.2]

/-- Range reduction permits every real argument through a positive natural scale. -/
theorem exp_range_reduction (x : ℝ) {k : ℕ} (hk : 0 < k) :
    Real.exp x = Real.exp (x / k) ^ k := by
  rw [← Real.exp_nat_mul]
  congr 1
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

theorem exp_scaled_mem {x b : ℝ} {N k : ℕ} {P J : Interval}
    (hk : 0 < k) (hN : 0 < N) (hx : |x / k| ≤ b) (hb : b ≤ 1)
    (hP : P.Mem (expSum N (x / k)))
    (hl : J.lo ≤ P.lo - expError N b) (hu : P.hi + expError N b ≤ J.hi) :
    (Interval.pow J k).Mem (Real.exp x) := by
  rw [exp_range_reduction x hk]
  exact Interval.mem_pow (exp_mem hN hx hb hP hl hu) k

theorem iteratedDeriv_exp (N : ℕ) : iteratedDeriv N Real.exp = Real.exp := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

theorem exp_taylor_eq {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    taylorWithinEval Real.exp n (Set.uIcc 0 x) 0 x = expSum (n + 1) x := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.symm)
    Real.contDiff_exp.contDiffAt (Set.left_mem_uIcc), iteratedDeriv_exp]
  simp [div_eq_mul_inv, mul_comm]

/-- The factorial remainder holds on the entire negative half-line. -/
theorem exp_negative_remainder {x : ℝ} (hx : x ≤ 0) (n : ℕ) :
    |Real.exp x - expSum (n + 1) x| ≤ |x| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  by_cases hx0 : x = 0
  · subst x
    have hs : expSum (n + 1) 0 = 1 := by
      unfold expSum
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        simp [zero_pow hj0]
      · simp
    simp [hs]
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (Ne.symm hx0) (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ (n + 1) Real.exp (Set.uIcc 0 x))
  rw [exp_taylor_eq hx0 n, iteratedDeriv_exp] at heq
  have hy0 : y ≤ 0 := by
    rw [Set.uIoo_of_ge hx] at hy
    exact hy.2.le
  have he : Real.exp y ≤ 1 := by simpa using Real.exp_le_exp.mpr hy0
  rw [heq, abs_div, abs_mul, abs_pow, sub_zero, abs_of_nonneg (Real.exp_pos y).le,
    Nat.abs_cast]
  exact div_le_div_of_nonneg_right
    (by simpa using mul_le_mul_of_nonneg_right he (pow_nonneg (abs_nonneg x) _))
    (by positivity)

end BstLean.Part197
