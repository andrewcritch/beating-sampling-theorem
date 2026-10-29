import BstLean.Part218SquaredKernel
import BstLean.Part218AngularMoments
import BstLean.Part132Upper

/-! The explicit second angular moment of the input norm kernel. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part29 BstLean.Part105 BstLean.Part130 BstLean.Part132

lemma reluSquarePair_measurable : Measurable reluSquarePair := by
  have hm : Measurable (fun p : ℝ × ((Fin 1 → ℝ) × (Fin 1 → ℝ)) =>
      relu (p.2.1 0) ^ 2 * relu ((p.1 • p.2.1 + sC p.1 • p.2.2) 0) ^ 2) := by
    unfold relu sC
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

noncomputable def bA1 (N : ℕ) : ℝ := (2 / π) / ((N : ℝ) * (N + 2))
noncomputable def bA2 (N : ℕ) : ℝ := (5 / 4 - 2 / π) / ((N : ℝ) * (N + 2))
noncomputable def bA0 (N : ℕ) : ℝ :=
  |1 / (4 * (N : ℝ) * (N + 2)) - 1 / (4 * (N : ℝ) ^ 2)|
noncomputable def angularJb (N : ℕ) : ℝ :=
  bA1 N ^ 2 * angularMoment N 1 + bA2 N ^ 2 * angularMoment N 2 + bA0 N ^ 2 +
    2 * bA1 N * bA2 N * √(angularMoment N 1 * angularMoment N 2) +
    2 * bA1 N * bA0 N * √(angularMoment N 1) + 2 * bA2 N * bA0 N * angularMoment N 1

lemma bA_nonneg (N : ℕ) : 0 ≤ bA1 N ∧ 0 ≤ bA2 N ∧ 0 ≤ bA0 N := by
  have hp : 2 / π ≤ (2 : ℝ) / 3 :=
    (div_le_div_iff₀ pi_pos (by norm_num)).mpr (by linarith [pi_gt_three])
  have hh : 0 ≤ (5 : ℝ) / 4 - 2 / π := by linarith
  unfold bA1 bA2 bA0
  exact ⟨by positivity, by positivity, abs_nonneg _⟩

theorem squaredAngular_second_moment {N : ℕ} (hN : 1 ≤ N) (i : Fin N) :
    (∫ u : Fin N → ℝ, squaredAngularB N (u i) ^ 2 ∂uniformSphere N) ≤ angularJb N := by
  have := uniformSphere_isProbability N hN
  obtain ⟨ha, hb, hd⟩ := bA_nonneg N
  let P : ℝ → ℝ := fun x => bA1 N * |x| + bA2 N * x ^ 2 + bA0 N
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hi : ∀ (f : ℝ → ℝ), Continuous f → Integrable (fun u : Fin N → ℝ => f (u i)) (uniformSphere N) :=
    fun f hf => sphere_cont_integrable hN (hf.comp (continuous_apply i))
  have hm : Measurable (fun u : Fin N → ℝ => squaredAngularB N (u i) ^ 2) := by
    unfold squaredAngularB
    exact (((reluSquarePair_measurable.comp (measurable_pi_apply i)).div_const _).sub_const _).pow_const 2
  have hpt : ∀ᵐ u ∂uniformSphere N, squaredAngularB N (u i) ^ 2 ≤ P (u i) ^ 2 := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    have h := pow_le_pow_left₀ (abs_nonneg _) (squaredAngularB_envelope hN (sphere_coordinate_abs hu i)) 2
    simpa only [sq_abs, P, bA1, bA2, bA0] using h
  have iB : Integrable (fun u : Fin N → ℝ => squaredAngularB N (u i) ^ 2) (uniformSphere N) :=
    (hi (fun x => P x ^ 2) (hP.pow 2)).mono' hm.aestronglyMeasurable (by
      filter_upwards [hpt] with u hu
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hu)
  have hu := integral_mono_ae iB (hi (fun x => P x ^ 2) (hP.pow 2)) hpt
  have e1 := sphere_coordinate_even hN i 1
  have e2 := sphere_coordinate_even hN i 2
  have hm1 : 0 ≤ angularMoment N 1 := by rw [← e1]; exact integral_nonneg fun _ => sq_nonneg _
  have hcs1 := (integral_abs_le_sqrt (measurable_pi_apply i)
    (hi (fun x => x ^ 2) (by fun_prop))).2
  have hcs3 := (integral_mul_le_sqrt (measurable_pi_apply i) ((measurable_pi_apply i).pow_const 2)
    (hi (fun x => x ^ 2) (by fun_prop))
    (hi (fun x => (x ^ 2) ^ 2) (by fun_prop))).2
  simp only [abs_pow, sq_abs, ← pow_mul] at hcs3
  rw [e1, e2, ← sqrt_mul hm1] at hcs3
  rw [e1] at hcs1
  have he : ∀ x : ℝ, P x ^ 2 = bA1 N ^ 2 * x ^ 2 + bA2 N ^ 2 * x ^ 4 + bA0 N ^ 2 +
      2 * bA1 N * bA2 N * (|x| * x ^ 2) + 2 * bA1 N * bA0 N * |x| +
      2 * bA2 N * bA0 N * x ^ 2 := by
    intro x
    dsimp [P]
    ring_nf
    rw [sq_abs]
  simp_rw [he] at hu
  repeat rw [integral_add (sphere_cont_integrable hN (by fun_prop))
    (sphere_cont_integrable hN (by fun_prop))] at hu
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul] at hu
  rw [e1, e2] at hu
  have hc3 := mul_le_mul_of_nonneg_left hcs3 (show 0 ≤ 2 * bA1 N * bA2 N by positivity)
  have hc1 := mul_le_mul_of_nonneg_left hcs1 (show 0 ≤ 2 * bA1 N * bA0 N by positivity)
  unfold angularJb
  linarith

end BstLean.Part218
#print axioms BstLean.Part218.squaredAngular_second_moment
