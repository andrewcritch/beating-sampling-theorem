import BstLean.Part193Interval
import BstLean.Part130Kappa
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Part 197: geometric remainders for arctangent and the exact ReLU kernel. -/
namespace BstLean.Part197

open MeasureTheory Set
open BstLean.Part193

noncomputable def atanSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, (-1 : ℝ) ^ j * x ^ (2 * j + 1) / (2 * j + 1)

theorem atan_geometric_identity (N : ℕ) (t : ℝ) :
    1 / (1 + t ^ 2) - ∑ j ∈ Finset.range N, (-(t ^ 2)) ^ j =
      (-(t ^ 2)) ^ N / (1 + t ^ 2) := by
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  have hg := geom_sum_mul_neg (-(t ^ 2)) N
  simp only [sub_neg_eq_add] at hg
  apply (eq_div_iff hd).mpr
  field_simp
  nlinarith [hg]

theorem integral_atanSum (N : ℕ) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, ∑ j ∈ Finset.range N, (-(t ^ 2)) ^ j) = atanSum N x := by
  unfold atanSum
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    have hid : (fun t : ℝ => (-(t ^ 2)) ^ j) =
        (fun t : ℝ => (-1 : ℝ) ^ j * t ^ (2 * j)) := by
      funext t
      rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul]
    rw [hid, intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (by omega : 2 * j + 1 ≠ 0), sub_zero]
    push_cast
    ring
  · intro j hj
    exact (by fun_prop : Continuous (fun t : ℝ => (-(t ^ 2)) ^ j)).intervalIntegrable _ _

theorem integral_atan_derivative (x : ℝ) :
    (∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2)) = Real.arctan x := by
  have hc : Continuous (fun t : ℝ => 1 / (1 + t ^ 2)) := by
    exact continuous_const.div (by fun_prop) (fun t => by positivity)
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => Real.hasDerivAt_arctan t) (hc.intervalIntegrable _ _)

/-- The bound is valid for every nonnegative argument and every finite order. -/
theorem atan_remainder {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    |Real.arctan x - atanSum N x| ≤ x ^ (2 * N + 1) / (2 * N + 1) := by
  have hc : Continuous (fun t : ℝ => 1 / (1 + t ^ 2)) := by
    exact continuous_const.div (by fun_prop) (fun t => by positivity)
  have hp : Continuous (fun t : ℝ => ∑ j ∈ Finset.range N, (-(t ^ 2)) ^ j) := by fun_prop
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hx
    (f := fun t : ℝ => 1 / (1 + t ^ 2) - ∑ j ∈ Finset.range N, (-(t ^ 2)) ^ j)
    (g := fun t : ℝ => t ^ (2 * N))
    (ae_of_all _ (fun t ht => by
      rw [Real.norm_eq_abs, atan_geometric_identity, abs_div, abs_pow, abs_neg,
        abs_of_nonneg (sq_nonneg t), ← pow_mul, abs_of_pos (by positivity : 0 < 1 + t ^ 2)]
      exact (div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
        (by nlinarith [mul_nonneg (pow_nonneg ht.1.le (2 * N)) (sq_nonneg t)])))
    ((by fun_prop : Continuous (fun t : ℝ => t ^ (2 * N))).intervalIntegrable _ _)
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hp.intervalIntegrable _ _),
    integral_atan_derivative, integral_atanSum, integral_pow] at h
  simpa only [Real.norm_eq_abs, zero_pow (by omega : 2 * N + 1 ≠ 0), sub_zero,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using h

theorem atan_mem {x : ℝ} {P J : Interval} (hx : 0 ≤ x) (N : ℕ)
    (hP : P.Mem (atanSum N x)) (hl : J.lo ≤ P.lo - x ^ (2 * N + 1) / (2 * N + 1))
    (hu : P.hi + x ^ (2 * N + 1) / (2 * N + 1) ≤ J.hi) : J.Mem (Real.arctan x) := by
  have h := abs_le.mp (atan_remainder hx N)
  constructor <;> linarith [hP.1, hP.2, h.1, h.2]

noncomputable def angleRatio (c : ℝ) : ℝ := Real.sqrt ((1 - c) / (1 + c))

/-- The half-angle parameter is in [0,1) on the positive overlap domain. -/
theorem angle_ratio_domain {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ angleRatio c ∧ angleRatio c < 1 := by
  have hd : 0 < 1 + c := by linarith
  have hq : (1 - c) / (1 + c) < 1 := (div_lt_one hd).mpr (by linarith)
  have hq0 : 0 ≤ (1 - c) / (1 + c) := div_nonneg (sub_nonneg.mpr hc1) hd.le
  exact ⟨Real.sqrt_nonneg _, by
    unfold angleRatio
    exact (Real.sqrt_lt hq0 zero_le_one).mpr (by simpa using hq)⟩

theorem arccos_half_angle {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Real.arccos c = 2 * Real.arctan (angleRatio c) := by
  have hd : 0 < 1 + c := by linarith
  have hq : 0 ≤ (1 - c) / (1 + c) := div_nonneg (by linarith) hd.le
  have hs : angleRatio c ^ 2 = (1 - c) / (1 + c) := Real.sq_sqrt hq
  have hdom := angle_ratio_domain hc hc1
  apply Real.arccos_eq_of_eq_cos
  · exact mul_nonneg (by norm_num) (Real.arctan_nonneg.mpr hdom.1)
  · have h := Real.arctan_lt_pi_div_two (angleRatio c)
    linarith
  · rw [Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 1 + angleRatio c ^ 2), hs]
    field_simp
    ring

theorem arccos_remainder {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (N : ℕ) :
    |Real.arccos c - 2 * atanSum N (angleRatio c)| ≤
      2 * (angleRatio c ^ (2 * N + 1) / (2 * N + 1)) := by
  rw [arccos_half_angle hc hc1, ← mul_sub, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left (atan_remainder (angle_ratio_domain hc hc1).1 N)
    (by norm_num)

noncomputable def kernelSlope (c : ℝ) : ℝ := (Real.pi - Real.arccos c) / Real.pi

noncomputable def kernelSlopeSum (N : ℕ) (c : ℝ) : ℝ :=
  (Real.pi - 2 * atanSum N (angleRatio c)) / Real.pi

noncomputable def kernelSum (N : ℕ) (c : ℝ) : ℝ :=
  (Real.sqrt (1 - c ^ 2) + c * (Real.pi - 2 * atanSum N (angleRatio c))) / Real.pi

/-- The slope is the derivative of the existing project kernel on its interior domain. -/
theorem kernel_slope_derivative {c : ℝ} (hc : -1 < c) (hc1 : c < 1) :
    HasDerivAt BstLean.Part130.kappa (kernelSlope c) c :=
  BstLean.Part130.hasDerivAt_kappa hc hc1

theorem kernel_slope_remainder {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (N : ℕ) :
    |kernelSlope c - kernelSlopeSum N c| ≤
      (2 * (angleRatio c ^ (2 * N + 1) / (2 * N + 1))) / Real.pi := by
  have h := arccos_remainder hc hc1 N
  have heq : kernelSlope c - kernelSlopeSum N c =
      -(Real.arccos c - 2 * atanSum N (angleRatio c)) / Real.pi := by
    unfold kernelSlope kernelSlopeSum
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right h Real.pi_pos.le

theorem kernel_remainder {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (N : ℕ) :
    |BstLean.Part130.kappa c - kernelSum N c| ≤
      c * (2 * (angleRatio c ^ (2 * N + 1) / (2 * N + 1))) / Real.pi := by
  have h := arccos_remainder hc hc1 N
  have heq : BstLean.Part130.kappa c - kernelSum N c =
      -c * (Real.arccos c - 2 * atanSum N (angleRatio c)) / Real.pi := by
    unfold BstLean.Part130.kappa kernelSum
    ring
  rw [heq, abs_div, abs_mul, abs_neg, abs_of_pos hc, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h hc.le) Real.pi_pos.le

end BstLean.Part197
