import BstLean.Part213Rows
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! An exponential generating series retains the zero singleton coefficient. -/
namespace BstLean.Part239
open BstLean.Part213
open PowerSeries

noncomputable def singletonSeries : PowerSeries ℝ :=
  PowerSeries.mk fun k => rowWeight (fun _ => 1) k / (k.factorial : ℝ)

noncomputable def seriesRowCount (m k : ℕ) : ℝ :=
  (k.factorial : ℝ) * PowerSeries.coeff k (singletonSeries ^ m)

lemma factorial_ne_zero_real (k : ℕ) : (k.factorial : ℝ) ≠ 0 := by
  exact_mod_cast k.factorial_ne_zero

lemma singletonSeries_derivative :
    PowerSeries.derivative singletonSeries = singletonSeries + PowerSeries.X - 1 := by
  ext k
  rw [PowerSeries.coeff_derivative]
  simp only [singletonSeries, PowerSeries.coeff_mk, map_sub, map_add,
    PowerSeries.coeff_X, PowerSeries.coeff_one]
  rcases k with _ | _ | k
  · norm_num [rowWeight]
  · norm_num [rowWeight]
  · simp only [rowWeight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hk : (k + 2 : ℝ) ≠ 0 := by positivity
    have hk3 : (k + 3 : ℝ) ≠ 0 := by positivity
    have hs : (k + 2 : ℕ) ≠ 0 := by omega
    have hs1 : (k + 2 : ℕ) ≠ 1 := by omega
    simp only [hs, hs1, if_false]
    field_simp [factorial_ne_zero_real, hk, hk3] <;> ring

lemma seriesRowCount_zero (k : ℕ) :
    seriesRowCount 0 k = if k = 0 then 1 else 0 := by
  simp only [seriesRowCount, pow_zero, PowerSeries.coeff_one]
  by_cases hk : k = 0 <;> simp [hk]

lemma factorial_choose_real {k i : ℕ} (hi : i ≤ k) :
    (k.factorial : ℝ) / ((i.factorial : ℝ) * ((k - i).factorial : ℝ)) = k.choose i := by
  have h : (k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ) = k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  field_simp [factorial_ne_zero_real]
  nlinarith

lemma seriesRowCount_succ (m k : ℕ) :
    seriesRowCount (m + 1) k =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * rowWeight (fun _ => 1) i *
        seriesRowCount m (k - i) := by
  rw [seriesRowCount, pow_succ', PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [singletonSeries, PowerSeries.coeff_mk]
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hf := factorial_choose_real hik
  dsimp only [seriesRowCount]
  have hi0 := factorial_ne_zero_real i
  have hki0 := factorial_ne_zero_real (k - i)
  have hfac : (k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ) = k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
  rw [← hfac]
  field_simp
  simp only [singletonSeries, div_eq_mul_inv]

theorem seriesRowCount_eq_rowEnvelope (m k : ℕ) :
    seriesRowCount m k = rowEnvelope (fun _ => 1) m k := by
  induction m generalizing k with
  | zero => exact seriesRowCount_zero k
  | succ m ih =>
    rw [seriesRowCount_succ, rowEnvelope]
    exact Finset.sum_congr rfl fun i _ => by rw [ih]

lemma seriesRowCount_order_zero (m : ℕ) : seriesRowCount m 0 = 1 := by
  have h0 : PowerSeries.constantCoeff singletonSeries = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [singletonSeries, PowerSeries.coeff_mk, rowWeight]
  simp [seriesRowCount, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]

lemma seriesRowCount_order_one (m : ℕ) : seriesRowCount m 1 = 0 := by
  simp [seriesRowCount, PowerSeries.coeff_one_pow, singletonSeries,
    PowerSeries.coeff_mk, rowWeight]

/-- Formal differentiation gives the order recurrence without a finite order cap. -/
theorem seriesRowCount_recurrence (p m : ℕ) :
    seriesRowCount (m + 1) (p + 2) = (m + 1 : ℝ) *
      (seriesRowCount (m + 1) (p + 1) - seriesRowCount m (p + 1) +
        (p + 1 : ℝ) * seriesRowCount m p) := by
  have hd : PowerSeries.derivative (singletonSeries ^ (m + 1)) =
      ((m + 1 : ℕ) : PowerSeries ℝ) *
        (singletonSeries ^ (m + 1) + singletonSeries ^ m * PowerSeries.X -
          singletonSeries ^ m) := by
    rw [PowerSeries.derivative_pow, Nat.add_sub_cancel, singletonSeries_derivative, pow_succ]
    push_cast
    ring
  have h := congrArg (PowerSeries.coeff (p + 1)) hd
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_natCast_mul,
    map_sub, map_add, PowerSeries.coeff_succ_mul_X] at h
  have hf := congrArg (fun x : ℝ => ((p + 1).factorial : ℝ) * x) h
  dsimp only [seriesRowCount]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hf ⊢
  nlinarith [hf]

#print axioms singletonSeries_derivative
#print axioms seriesRowCount_eq_rowEnvelope
#print axioms seriesRowCount_recurrence
end BstLean.Part239
