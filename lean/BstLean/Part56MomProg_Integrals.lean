import BstLean.Part56MomProg_Basic

/-! Exact integral reductions for the Part 56 moment program. -/

namespace BstLean.Part56.MomProg

open MeasureTheory
open BstLean.Part56
open BstLean.Part29 (uniformSphere)
open BstLean.Part50 (ZKA qA)

variable {n : ℕ}

theorem sphere_integrable (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

theorem taylor_one_le (K : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    1 ≤ BstLean.Part37.taylorExp K z := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (K + 1)) =>
      div_nonneg (pow_nonneg hz i) (Nat.cast_nonneg i.factorial))
    (Finset.mem_range.mpr (show 0 < K + 1 by omega))
  simpa [BstLean.Part37.taylorExp] using h

theorem normalizer_one_le (hn : 1 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (v : Fin n → ℝ) : 1 ≤ ZKA n K (rk1 t v) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hc : Continuous (fun x => BstLean.Part37.taylorExp K (qA (rk1 t v) x)) := by
    unfold BstLean.Part37.taylorExp qA
    fun_prop
  have hi := integral_mono (integrable_const (1 : ℝ)) (sphere_integrable hn hc)
    (fun x => taylor_one_le K (rk1_psd t ht v x))
  simpa [ZKA] using hi

theorem integral_surrogate (hn : 1 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (v : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    (∫ x, f x ∂surrRK n K t v) =
      (∫ x, f x * BstLean.Part37.taylorExp K (t * (∑ i, v i * x i) ^ 2)
        ∂uniformSphere n) / ZKA n K (rk1 t v) := by
  have hZ : 0 ≤ ZKA n K (rk1 t v) :=
    le_trans zero_le_one (normalizer_one_le hn K t ht v)
  have hc : Continuous (fun x =>
      BstLean.Part37.taylorExp K (qA (rk1 t v) x) / ZKA n K (rk1 t v)) := by
    unfold BstLean.Part37.taylorExp qA
    fun_prop
  unfold surrRK BstLean.Part50.binghamKA
  rw [integral_withDensity_eq_integral_toReal_smul
    hc.measurable.ennreal_ofReal (by simp)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg
    (zero_le_one.trans (taylor_one_le K (rk1_psd t ht v _))) hZ),
    smul_eq_mul, mul_comm _ (f _), ← mul_div_assoc, qA_rk1]
  exact integral_div _ _

/-- The scalar moment numerator, before the directional sphere moments are evaluated. -/
noncomputable def scalarNumerator (K a : ℕ) (t : ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1), (t ^ i / (i.factorial : ℝ)) *
    ∫ x, (∑ j, v j * x j) ^ (2 * (a + i)) ∂uniformSphere n

theorem scalarNumerator_integral (hn : 1 ≤ n) (K a : ℕ) (t : ℝ) (v : Fin n → ℝ) :
    (∫ x, (∑ j, v j * x j) ^ (2 * a) *
      BstLean.Part37.taylorExp K (t * (∑ j, v j * x j) ^ 2) ∂uniformSphere n) =
      scalarNumerator K a t v := by
  classical
  have hp (x : Fin n → ℝ) : (∑ j, v j * x j) ^ (2 * a) *
      BstLean.Part37.taylorExp K (t * (∑ j, v j * x j) ^ 2) =
      ∑ i ∈ Finset.range (K + 1), (t ^ i / (i.factorial : ℝ)) *
        (∑ j, v j * x j) ^ (2 * (a + i)) := by
    unfold BstLean.Part37.taylorExp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, ← pow_mul, Nat.mul_add, pow_add]
    ring
  simp_rw [hp]
  rw [integral_finsetSum]
  · unfold scalarNumerator
    apply Finset.sum_congr rfl
    intro i _
    exact integral_const_mul _ _
  · intro i _
    apply Integrable.const_mul
    apply sphere_integrable hn
    fun_prop

theorem normalizer_scalarNumerator (hn : 1 ≤ n) (K : ℕ) (t : ℝ) (v : Fin n → ℝ) :
    ZKA n K (rk1 t v) = scalarNumerator K 0 t v := by
  rw [← scalarNumerator_integral hn]
  simp [ZKA, qA_rk1]

theorem scalar_moment_ratio (hn : 1 ≤ n) (K a : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (v : Fin n → ℝ) :
    (∫ x, (∑ j, v j * x j) ^ (2 * a) ∂surrRK n K t v) =
      scalarNumerator K a t v / scalarNumerator K 0 t v := by
  rw [integral_surrogate hn K t ht v, scalarNumerator_integral hn,
    normalizer_scalarNumerator hn]

end BstLean.Part56.MomProg
