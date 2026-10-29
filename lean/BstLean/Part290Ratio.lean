import BstLean.Part271AngularScale
import Mathlib.Topology.Order.MonotoneConvergence

/-! Uniform first-layer radius bounds from the exact even-dimensional recurrence.
The proof uses two monotone normalizations and their common limit, with no
dimension table and no numerical Gamma evaluation. -/
namespace BstLean.Part290
open Real Filter
open scoped Topology
open BstLean.Part137 BstLean.Part159 BstLean.Part218

noncomputable def radiusRatio (k : ℕ) : ℝ :=
  4 * π * ((k : ℝ) + 1) * cN (2 * (k + 1)) ^ 2

theorem centre_step (k : ℕ) :
    cN (2 * (k + 1 + 1)) =
      cN (2 * (k + 1)) * (2 * ((k : ℝ) + 1) / (2 * ((k : ℝ) + 1) + 1)) := by
  rw [cN_even_succ (k + 1), cN_even_succ k,
    Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
  push_cast
  ring

theorem radiusRatio_nonneg (k : ℕ) : 0 ≤ radiusRatio k := by
  unfold radiusRatio
  positivity

theorem radiusRatio_step (k : ℕ) :
    radiusRatio (k + 1) = radiusRatio k *
      (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) / (2 * ((k : ℝ) + 1) + 1) ^ 2) := by
  unfold radiusRatio
  rw [centre_step]
  push_cast
  field_simp
  ring

theorem radiusRatio_rough (k : ℕ) :
    1 ≤ radiusRatio k ∧ radiusRatio k ≤ 1 + 1 / ((k : ℝ) + 1) := by
  obtain ⟨hl, hu⟩ := rN_window (N := 2 * (k + 1)) (by omega)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hp := Real.pi_pos
  push_cast at hl hu
  have hl' := (div_le_iff₀ hp).mp hl
  have hd : 0 < 2 * ((k : ℝ) + 1) - 1 := by linarith
  have hu' := (le_div_iff₀ (by exact mul_pos hp hd :
    0 < π * (2 * ((k : ℝ) + 1) - 1))).mp hu
  constructor
  · unfold radiusRatio
    nlinarith only [hl']
  · calc
      radiusRatio k ≤ (((k : ℝ) + 1) + 1) / ((k : ℝ) + 1) := by
        apply (le_div_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
        have hr := radiusRatio_nonneg k
        have hbound : radiusRatio k * (2 * (k : ℝ) + 1) ≤ 2 * ((k : ℝ) + 1) := by
          unfold radiusRatio
          nlinarith only [hu']
        nlinarith [mul_nonneg hk (sub_nonneg.mpr (show 1 ≤ radiusRatio k by
          unfold radiusRatio; nlinarith only [hl']))]
      _ = 1 + 1 / ((k : ℝ) + 1) := by field_simp

theorem radiusRatio_limit : Tendsto radiusRatio atTop (𝓝 1) := by
  have hu : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using ((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have h := tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (1 : ℝ)))
    hu
    (fun k => (radiusRatio_rough k).1) (fun k => (radiusRatio_rough k).2)
  simpa using h

noncomputable def upperNormalized (k : ℕ) : ℝ :=
  radiusRatio k * (1 - 1 / (4 * ((k : ℝ) + 1)))

noncomputable def lowerNormalized (k : ℕ) : ℝ :=
  radiusRatio k / (1 + 1 / (4 * ((k : ℝ) + 1)))

theorem upperNormalized_mono : Monotone upperNormalized := by
  apply monotone_nat_of_le_succ
  intro k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hr := radiusRatio_nonneg k
  unfold upperNormalized
  rw [radiusRatio_step]
  push_cast
  have he : radiusRatio k *
      (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) / (2 * ((k : ℝ) + 1) + 1) ^ 2) *
      (1 - 1 / (4 * ((k : ℝ) + 1 + 1))) -
      radiusRatio k * (1 - 1 / (4 * ((k : ℝ) + 1))) =
      radiusRatio k / (4 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) ^ 2) := by
    field_simp
    <;> ring
  have hh : 0 ≤ radiusRatio k / (4 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) ^ 2) := by
    positivity
  linarith only [he, hh]

theorem lowerNormalized_anti : Antitone lowerNormalized := by
  apply antitone_nat_of_succ_le
  intro k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hr := radiusRatio_nonneg k
  unfold lowerNormalized
  rw [radiusRatio_step]
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have he : radiusRatio k * (1 + 1 / (4 * ((k : ℝ) + 1 + 1))) -
      radiusRatio k *
        (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) / (2 * ((k : ℝ) + 1) + 1) ^ 2) *
        (1 + 1 / (4 * ((k : ℝ) + 1))) =
      radiusRatio k / (4 * ((k : ℝ) + 2) * (2 * (k : ℝ) + 3) ^ 2) := by
    field_simp
    <;> ring
  have hh : 0 ≤ radiusRatio k / (4 * ((k : ℝ) + 2) * (2 * (k : ℝ) + 3) ^ 2) := by
    positivity
  linarith only [he, hh]

theorem inverse_four_limit :
    Tendsto (fun k : ℕ => 1 / (4 * ((k : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
  have he : (fun k : ℕ => (1 : ℝ) / (4 * ((k : ℝ) + 1))) =
      (fun k : ℕ => (1 / ((k : ℝ) + 1)) / 4) := by
    funext k
    field_simp
  rw [he]
  simpa only [zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 4

theorem radiusRatio_sharp (k : ℕ) :
    1 + 1 / (4 * ((k : ℝ) + 1)) ≤ radiusRatio k ∧
    radiusRatio k ≤ 1 / (1 - 1 / (4 * ((k : ℝ) + 1))) := by
  have hu : Tendsto upperNormalized atTop (𝓝 1) := by
    change Tendsto (fun k => radiusRatio k * (1 - 1 / (4 * ((k : ℝ) + 1)))) _ _
    simpa only [sub_zero, mul_one] using radiusRatio_limit.mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub inverse_four_limit)
  have hl : Tendsto lowerNormalized atTop (𝓝 1) := by
    change Tendsto (fun k => radiusRatio k / (1 + 1 / (4 * ((k : ℝ) + 1)))) _ _
    have hi := ((tendsto_const_nhds (x := (1 : ℝ))).add inverse_four_limit).inv₀
      (by norm_num : (1 : ℝ)+0 ≠ 0)
    simpa only [add_zero, inv_one, mul_one, div_eq_mul_inv] using radiusRatio_limit.mul hi
  have hU := upperNormalized_mono.ge_of_tendsto hu k
  have hL := lowerNormalized_anti.le_of_tendsto hl k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  constructor
  · simpa [lowerNormalized] using (le_div_iff₀
      (by positivity : 0 < 1 + 1 / (4 * ((k : ℝ) + 1)))).mp hL
  · have hp : 0 < 1 - 1 / (4 * ((k : ℝ) + 1)) := by
      have : 1 / (4 * ((k : ℝ) + 1)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      linarith
    exact (le_div_iff₀ hp).mpr hU

end BstLean.Part290
