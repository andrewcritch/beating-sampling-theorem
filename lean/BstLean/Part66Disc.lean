import BstLean.Part48Defs

/-!
# Part 66: the discrete mean of a trigonometric polynomial

For `IsTrig h F` and `N = 2h + 1`, the sum of `F` over the `N` equally spaced points
`u + 2πk/N` does not depend on `u` (it is `N a₀`). With `F ≥ 0` this gives
`F u ≤ Σ_k F(2πk/N)`: the maximum is at most `N` times the discrete mean.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part66

open BstLean.Part48 (IsTrig)
open Finset

/-- A nontrivial `N`-th root of unity sums to zero over a full period, shifted by a phase. -/
lemma exp_sum_zero (N j : ℕ) (hj0 : 0 < j) (hjN : j < N) (u : ℝ) :
    ∑ k ∈ range N, Complex.exp (((j : ℝ) * (u + 2 * Real.pi * k / N) : ℝ) * Complex.I) = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le j) hjN)
  set z : ℂ := Complex.exp ((2 * Real.pi * j / N : ℝ) * Complex.I) with hz
  have hterm : ∀ k : ℕ, Complex.exp (((j : ℝ) * (u + 2 * Real.pi * k / N) : ℝ) * Complex.I) =
      Complex.exp (((j : ℝ) * u : ℝ) * Complex.I) * z ^ k := by
    intro k
    rw [hz, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hz1 : z ≠ 1 := by
    rw [hz]
    intro h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hre : (2 * Real.pi * j / N : ℝ) = n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simpa using this
    have hpi := Real.pi_pos
    have hjn : (j : ℝ) / N = n := by
      field_simp at hre ⊢; nlinarith [hre]
    have h0 : (0 : ℝ) < j / N := by
      have : (0 : ℝ) < j := by exact_mod_cast hj0
      positivity
    have h1 : (j : ℝ) / N < 1 := by
      rw [div_lt_one hN]; exact_mod_cast hjN
    rw [hjn] at h0 h1
    have h0' : (0 : ℤ) < n := by exact_mod_cast h0
    have h1' : n < (1 : ℤ) := by exact_mod_cast h1
    omega
  have hzN : z ^ N = 1 := by
    rw [hz, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨j, ?_⟩
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  rw [geom_sum_eq hz1, hzN, sub_self, zero_div, mul_zero]

lemma cos_sum_zero (N j : ℕ) (hj0 : 0 < j) (hjN : j < N) (u : ℝ) :
    ∑ k ∈ range N, Real.cos ((j : ℝ) * (u + 2 * Real.pi * k / N)) = 0 := by
  have := congrArg Complex.re (exp_sum_zero N j hj0 hjN u)
  rw [Complex.re_sum] at this
  simp only [Complex.exp_ofReal_mul_I_re] at this
  exact this

lemma sin_sum_zero (N j : ℕ) (hj0 : 0 < j) (hjN : j < N) (u : ℝ) :
    ∑ k ∈ range N, Real.sin ((j : ℝ) * (u + 2 * Real.pi * k / N)) = 0 := by
  have := congrArg Complex.im (exp_sum_zero N j hj0 hjN u)
  rw [Complex.im_sum] at this
  simp only [Complex.exp_ofReal_mul_I_im] at this
  exact this

/-- The sum of a trigonometric polynomial of degree `≤ h` over `2h+1` equally spaced points is
`(2h+1) a₀`. -/
lemma trig_sum_eq (h : ℕ) (a b : ℕ → ℝ) (u : ℝ) :
    ∑ k ∈ range (2 * h + 1), ∑ j ∈ range (h + 1),
      (a j * Real.cos (j * (u + 2 * Real.pi * k / (2 * h + 1 : ℕ))) +
        b j * Real.sin (j * (u + 2 * Real.pi * k / (2 * h + 1 : ℕ)))) =
      (2 * h + 1 : ℕ) * a 0 := by
  rw [Finset.sum_comm]
  rw [Finset.sum_range_succ']
  have hrest : ∑ j ∈ range h, ∑ k ∈ range (2 * h + 1),
      (a (j + 1) * Real.cos (((j + 1 : ℕ) : ℝ) * (u + 2 * Real.pi * k / (2 * h + 1 : ℕ))) +
        b (j + 1) * Real.sin (((j + 1 : ℕ) : ℝ) * (u + 2 * Real.pi * k / (2 * h + 1 : ℕ)))) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : j < h := Finset.mem_range.mp hj
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      cos_sum_zero _ _ (Nat.succ_pos j) (by omega), sin_sum_zero _ _ (Nat.succ_pos j) (by omega)]
    ring
  rw [hrest]
  simp

/-- **Shift invariance of the discrete sum.** -/
theorem trig_shift_sum (h : ℕ) (F : ℝ → ℝ) (hF : IsTrig h F) (u : ℝ) :
    ∑ k ∈ range (2 * h + 1), F (u + 2 * Real.pi * k / (2 * h + 1 : ℕ)) =
      ∑ k ∈ range (2 * h + 1), F (2 * Real.pi * k / (2 * h + 1 : ℕ)) := by
  obtain ⟨a, b, hab⟩ := hF
  simp_rw [hab]
  have := trig_sum_eq h a b u
  have h0 := trig_sum_eq h a b 0
  simp only [zero_add] at h0
  rw [this, h0]

/-- **Maximum at most `N` times the discrete mean**: for `F ≥ 0`,
`F u ≤ Σ_{k < 2h+1} F(2πk/(2h+1))`. -/
theorem trig_le_disc_sum (h : ℕ) (F : ℝ → ℝ) (hF : IsTrig h F) (hF0 : ∀ s, 0 ≤ F s) (u : ℝ) :
    F u ≤ ∑ k ∈ range (2 * h + 1), F (2 * Real.pi * k / (2 * h + 1 : ℕ)) := by
  rw [← trig_shift_sum h F hF u]
  have h0 : (0 : ℕ) ∈ range (2 * h + 1) := Finset.mem_range.mpr (by omega)
  have := Finset.single_le_sum (f := fun k : ℕ => F (u + 2 * Real.pi * k / (2 * h + 1 : ℕ)))
    (fun k _ => hF0 _) h0
  simpa using this

end BstLean.Part66
