import BstLean.Part56MomProg_Sphere

/-! Exact rational scalar moments and their recurrence. -/

namespace BstLean.Part56.MomProg

open MeasureTheory
open BstLean.Part56

def scalarQ (n a : ℕ) : ℚ :=
  ((2 * a - 1).doubleFactorial : ℚ) /
    ∏ i ∈ Finset.range a, ((n : ℚ) + 2 * i)

theorem scalarQ_zero (n : ℕ) : scalarQ n 0 = 1 := by simp [scalarQ]

theorem scalarQ_cast (n a : ℕ) :
    (scalarQ n a : ℝ) =
      BstLean.Part29.gaussMom (2 * a) / BstLean.Part36.rhoD n a := by
  simp [scalarQ, BstLean.Part29.gaussMom, BstLean.Part36.rhoD]

theorem scalarQ_den_pos {n : ℕ} (hn : 1 ≤ n) (a : ℕ) :
    0 < ∏ i ∈ Finset.range a, ((n : ℚ) + 2 * i) := by
  apply Finset.prod_pos
  intro i _
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  positivity

theorem scalarQ_nonneg (n a : ℕ) : 0 ≤ scalarQ n a := by
  unfold scalarQ
  positivity

theorem scalarQ_succ {n : ℕ} (hn : 1 ≤ n) (a : ℕ) :
    scalarQ n (a + 1) = scalarQ n a * ((2 * a + 1 : ℕ) : ℚ) / (n + 2 * a) := by
  have hd := (scalarQ_den_pos hn a).ne'
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : (n : ℚ) + 2 * a ≠ 0 := by positivity
  unfold scalarQ
  rw [Finset.prod_range_succ, show 2 * (a + 1) - 1 = 2 * a + 1 by omega,
    Nat.doubleFactorial_add_one]
  push_cast
  field_simp

noncomputable def scalarTilt (n K a : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1), t ^ i / (i.factorial : ℝ) * (scalarQ n (a + i) : ℝ)

theorem scalarNumerator_eq {n : ℕ} (hn : 1 ≤ n) (K a : ℕ) (t : ℝ)
    (v : Fin n → ℝ) (hv : UnitV v) :
    scalarNumerator K a t v = scalarTilt n K a t := by
  unfold scalarNumerator scalarTilt
  apply Finset.sum_congr rfl
  intro i _
  rw [sphere_directional_moment hn v hv, scalarQ_cast]

theorem scalarTilt_normalizer {n : ℕ} (hn : 1 ≤ n) (K : ℕ) (t : ℝ)
    (v : Fin n → ℝ) (hv : UnitV v) :
    BstLean.Part50.ZKA n K (rk1 t v) = scalarTilt n K 0 t := by
  rw [normalizer_scalarNumerator hn, scalarNumerator_eq hn K 0 t v hv]

theorem scalarTilt_one_le (n K : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ scalarTilt n K 0 t := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (K + 1)) => mul_nonneg
      (div_nonneg (pow_nonneg ht i) (Nat.cast_nonneg i.factorial))
      (Rat.cast_nonneg.mpr (scalarQ_nonneg n (0 + i))))
    (Finset.mem_range.mpr (show 0 < K + 1 by omega))
  simpa [scalarTilt, scalarQ_zero] using h

theorem scalar_surrogate_moment {n : ℕ} (hn : 1 ≤ n) (K a : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    (∫ x, (∑ j, v j * x j) ^ (2 * a) ∂surrRK n K t v) =
      scalarTilt n K a t / scalarTilt n K 0 t := by
  rw [scalar_moment_ratio hn K a t ht v,
    scalarNumerator_eq hn K a t v hv, scalarNumerator_eq hn K 0 t v hv]

end BstLean.Part56.MomProg
