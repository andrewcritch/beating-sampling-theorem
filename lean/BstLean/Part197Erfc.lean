import BstLean.Part197Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Part 197: the complementary error function and its factorial remainder.
The definition uses the exact Gaussian integral, with no numerical premise. -/
namespace BstLean.Part197

open MeasureTheory Set
open BstLean.Part193

noncomputable def erfc (z : ℝ) : ℝ :=
  1 - (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2))

noncomputable def erfSum (N : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    (-1 : ℝ) ^ j * z ^ (2 * j + 1) / ((j.factorial : ℝ) * (2 * j + 1))

noncomputable def erfcSum (N : ℕ) (z : ℝ) : ℝ :=
  1 - (2 / Real.sqrt Real.pi) * erfSum N z

noncomputable def erfcError (N : ℕ) (z : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * (z ^ (2 * N + 1) / ((N.factorial : ℝ) * (2 * N + 1)))

theorem integral_expSum (N : ℕ) (z : ℝ) :
    (∫ t in (0 : ℝ)..z, expSum N (-(t ^ 2))) = erfSum N z := by
  unfold expSum erfSum
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    have hid : (fun t : ℝ => (-(t ^ 2)) ^ j / (j.factorial : ℝ)) =
        (fun t : ℝ => (-1 : ℝ) ^ j * t ^ (2 * j) / (j.factorial : ℝ)) := by
      funext t
      rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul]
    rw [hid, intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
      integral_pow]
    simp only [zero_pow (by omega : 2 * j + 1 ≠ 0), sub_zero]
    push_cast
    have hf : (j.factorial : ℝ) ≠ 0 := by positivity
    have hd : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · intro j hj
    exact (by fun_prop : Continuous (fun t : ℝ => (-(t ^ 2)) ^ j /
      (j.factorial : ℝ))).intervalIntegrable _ _

/-- The integrated exponential remainder gives the exact remainder in the paper. -/
theorem erf_integral_remainder {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    |(∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2))) - erfSum (n + 1) z| ≤
      z ^ (2 * (n + 1) + 1) / (((n + 1).factorial : ℝ) * (2 * (n + 1) + 1)) := by
  have he : IntervalIntegrable (fun t : ℝ => Real.exp (-(t ^ 2))) volume 0 z :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(t ^ 2)))).intervalIntegrable _ _
  have hp : IntervalIntegrable (fun t : ℝ => expSum (n + 1) (-(t ^ 2))) volume 0 z := by
    unfold expSum
    exact (by fun_prop : Continuous (fun t : ℝ =>
      ∑ j ∈ Finset.range (n + 1), (-(t ^ 2)) ^ j / (j.factorial : ℝ))).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun t : ℝ => t ^ (2 * (n + 1)) /
      ((n + 1).factorial : ℝ)) volume 0 z :=
    (by fun_prop : Continuous (fun t : ℝ => t ^ (2 * (n + 1)) /
      ((n + 1).factorial : ℝ))).intervalIntegrable _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le hz
    (f := fun t : ℝ => Real.exp (-(t ^ 2)) - expSum (n + 1) (-(t ^ 2)))
    (g := fun t : ℝ => t ^ (2 * (n + 1)) / ((n + 1).factorial : ℝ))
    (ae_of_all _ (fun t ht => by
      have hr := exp_negative_remainder (x := -(t ^ 2)) (by nlinarith) n
      simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg t), ← pow_mul]
        using hr)) hb
  rw [intervalIntegral.integral_sub he hp, integral_expSum,
    intervalIntegral.integral_div, integral_pow] at h
  simp only [Real.norm_eq_abs, zero_pow (by omega : 2 * (n + 1) + 1 ≠ 0), sub_zero] at h
  push_cast at h ⊢
  convert h using 1
  rw [div_div, mul_comm (2 * ((n : ℝ) + 1) + 1) ((n + 1).factorial : ℝ)]

theorem erfc_remainder {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    |erfc z - erfcSum (n + 1) z| ≤ erfcError (n + 1) z := by
  have h := erf_integral_remainder hz n
  have hp : 0 ≤ 2 / Real.sqrt Real.pi := by positivity
  have heq : erfc z - erfcSum (n + 1) z =
      -(2 / Real.sqrt Real.pi) *
        ((∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2))) - erfSum (n + 1) z) := by
    unfold erfc erfcSum
    ring
  rw [heq, abs_mul, abs_neg, abs_of_nonneg hp]
  simpa only [erfcError, Nat.cast_add, Nat.cast_one] using
    mul_le_mul_of_nonneg_left h hp

theorem erfc_mem {z : ℝ} {P J : Interval} (hz : 0 ≤ z) (n : ℕ)
    (hP : P.Mem (erfcSum (n + 1) z))
    (hl : J.lo ≤ P.lo - erfcError (n + 1) z)
    (hu : P.hi + erfcError (n + 1) z ≤ J.hi) : J.Mem (erfc z) := by
  have h := abs_le.mp (erfc_remainder hz n)
  constructor <;> linarith [hP.1, hP.2, h.1, h.2]

/-- The same function equals the normalized Gaussian upper-tail integral. -/
theorem erfc_eq_tail {z : ℝ} (hz : 0 ≤ z) :
    erfc z = (2 / Real.sqrt Real.pi) * ∫ t in Ioi z, Real.exp (-(t ^ 2)) := by
  have hi : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hsub := intervalIntegral.integral_Ioi_sub_Ioi hi.integrableOn hz
  have hfull : (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2))) = Real.sqrt Real.pi / 2 := by
    simpa using integral_gaussian_Ioi (1 : ℝ)
  rw [hfull] at hsub
  unfold erfc
  rw [← hsub]
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

theorem erfc_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ erfc z := by
  rw [erfc_eq_tail hz]
  exact mul_nonneg (by positivity) (integral_nonneg (fun t => (Real.exp_pos _).le))

/-- The exact 301-term certificate has the stated exponent 603. -/
theorem erfc_paper_remainder {z : ℝ} (hz : 0 ≤ z) :
    |erfc z - erfcSum 301 z| ≤
      (2 / Real.sqrt Real.pi) * (z ^ 603 / ((Nat.factorial 301 : ℝ) * 603)) := by
  have h := erfc_remainder hz 300
  change |erfc z - erfcSum 301 z| ≤
    (2 / Real.sqrt Real.pi) * (z ^ 603 / ((Nat.factorial 301 : ℝ) * (2 * (301 : ℝ) + 1))) at h
  rw [show (2 * (301 : ℝ) + 1) = 603 by norm_num] at h
  exact h

end BstLean.Part197
