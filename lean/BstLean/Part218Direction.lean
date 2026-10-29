import BstLean.Part218DirectionRow
import BstLean.Part218InputVariance

/-! The directional Markov statistic has the exact expectation in P10e. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part105 BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part140 BstLean.Part141 BstLean.Part205 BstLean.Part214

lemma direction_square_rows {N m : ℕ} (hN : 1 ≤ N) {u : Fin N → ℝ} (hu : normSq u = 1)
    {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun M : Matrix (Fin m) (Fin N) ℝ =>
      dotp (reluV (M.mulVec u)) (h1bar M) ^ 2) (gaussMat m N v) ∧
    (∫ M : Matrix (Fin m) (Fin N) ℝ, dotp (reluV (M.mulVec u)) (h1bar M) ^ 2 ∂gaussMat m N v) =
      (m : ℝ) * (cN N ^ 2 * v ^ 2 * ((N : ℝ) + 2) / 2) +
        (m : ℝ) * ((m : ℝ) - 1) * (v * N * cN N ^ 2) ^ 2 := by
  have he : ∀ M : Matrix (Fin m) (Fin N) ℝ,
      dotp (reluV (M.mulVec u)) (h1bar M) = ∑ i, directionRow N u (rowOf i M) := fun _ => rfl
  simp_rw [he]
  obtain ⟨hi, hh⟩ := rows_sum_sq (m := m) v (directionRow N u)
    (directionRow_measurable hN u) (directionRow_square hN hu hv).1
  exact ⟨hi, by rw [hh, (directionRow_square hN hu hv).2, directionRow_mean hN hu hv]⟩

lemma direction_square_joint {N m : ℕ} (hN : 1 ≤ N) :
    Integrable (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) =>
      dotp (reluV (p.1.mulVec p.2)) (h1bar p.1) ^ 2)
      ((gaussMat m N (2 / (N : ℝ))).prod (uniformSphere N)) := by
  have := uniformSphere_isProbability N hN
  have hm : Measurable (fun p : (Fin N → ℝ) × Matrix (Fin m) (Fin N) ℝ =>
      dotp (reluV (p.2.mulVec p.1)) (h1bar p.2) ^ 2) := by
    have mg : Measurable (fun p : (Fin N → ℝ) × Matrix (Fin m) (Fin N) ℝ =>
        reluV (p.2.mulVec p.1)) := by
      apply measurable_reluV.comp
      unfold Matrix.mulVec dotProduct
      fun_prop
    exact (measurable_dotp_comp mg ((measurable_h1bar hN).comp measurable_snd)).pow_const 2
  have hi : Integrable (fun p : (Fin N → ℝ) × Matrix (Fin m) (Fin N) ℝ =>
      dotp (reluV (p.2.mulVec p.1)) (h1bar p.2) ^ 2)
      ((uniformSphere N).prod (gaussMat m N (2 / (N : ℝ)))) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    constructor
    · filter_upwards [uniformSphere_ae_sphere N] with u hu
      exact (direction_square_rows hN hu (by positivity)).1
    · have he : ∀ᵐ u ∂uniformSphere N,
          (∫ M : Matrix (Fin m) (Fin N) ℝ, ‖dotp (reluV (M.mulVec u)) (h1bar M) ^ 2‖
            ∂gaussMat m N (2 / (N : ℝ))) =
          (m : ℝ) * (cN N ^ 2 * (2 / (N : ℝ)) ^ 2 * ((N : ℝ) + 2) / 2) +
            (m : ℝ) * ((m : ℝ) - 1) * ((2 / (N : ℝ)) * N * cN N ^ 2) ^ 2 := by
        filter_upwards [uniformSphere_ae_sphere N] with u hu
        simp only [Real.norm_of_nonneg (sq_nonneg _)]
        exact (direction_square_rows hN hu (by positivity)).2
      apply (integrable_const _).congr
      filter_upwards [he] with u hu
      exact hu.symm
  exact hi.swap

lemma worldDirection_eq {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) :
    worldDirection M =
      (∫ u, dotp (reluV (M.mulVec u)) (h1bar M) ^ 2 ∂uniformSphere N) - normSq (h1bar M) ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hc : Continuous (fun u => dotp (reluV (M.mulVec u)) (h1bar M)) :=
    continuous_dotp.comp ((continuous_h1_u M).prodMk continuous_const)
  have he : ∀ u : Fin N → ℝ, (∑ i, h1bar M i * centeredFirst M i u) =
      dotp (reluV (M.mulVec u)) (h1bar M) - normSq (h1bar M) := by
    intro u
    unfold centeredFirst dotp normSq
    simp only [mul_sub, Finset.sum_sub_distrib, pow_two]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hm : (∫ u, dotp (reluV (M.mulVec u)) (h1bar M) ∂uniformSphere N) = normSq (h1bar M) := by
    unfold dotp normSq
    have hi : ∀ i : Fin m, Integrable (fun u : Fin N → ℝ =>
        reluV (M.mulVec u) i * h1bar M i) (uniformSphere N) := fun i =>
      (sphere_cont_integrable hN (show Continuous (fun u => reluV (M.mulVec u) i) from
        (continuous_apply i).comp (continuous_h1_u M))).mul_const _
    rw [integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_mul_const]
    change h1bar M i * h1bar M i = h1bar M i ^ 2
    ring
  unfold worldDirection centeredGram
  simp_rw [he]
  rw [(integral_sq_sub_const (sphere_cont_integrable hN hc)
    (sphere_cont_integrable hN (hc.pow 2)) (normSq (h1bar M))).2, hm]
  ring

/-- This exact mean supplies the directional Markov term without an assumed expectation. -/
theorem worldDirection_mean {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (worldDirection (N := N) (m := m)) (gaussMat m N (2 / (N : ℝ))) ∧
    (∫ M : Matrix (Fin m) (Fin N) ℝ, worldDirection M ∂gaussMat m N (2 / (N : ℝ))) =
      2 * (m : ℝ) * cN N ^ 2 * (N + 2) / (N : ℝ) ^ 2 * (1 - 2 * N * cN N ^ 2) := by
  have := uniformSphere_isProbability N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hj := direction_square_joint (m := m) hN
  have hi := hj.integral_prod_left
  have hQ := firstQ_second hN hm
  have hB : ∀ M : Matrix (Fin m) (Fin N) ℝ,
      normSq (h1bar M) ^ 2 = (2 * N * cN N ^ 2) ^ 2 * firstQ M ^ 2 := by
    intro M
    rw [normSq_h1bar hN, firstQ_rows hN hm]
    field_simp <;> ring
  have iB : Integrable (fun M : Matrix (Fin m) (Fin N) ℝ => normSq (h1bar M) ^ 2)
      (gaussMat m N (2 / (N : ℝ))) := by
    simp_rw [hB]
    exact hQ.1.const_mul _
  have hD : worldDirection (N := N) (m := m) = fun M =>
      (∫ u, dotp (reluV (M.mulVec u)) (h1bar M) ^ 2 ∂uniformSphere N) - normSq (h1bar M) ^ 2 :=
    funext (worldDirection_eq hN)
  rw [hD]
  refine ⟨hi.sub iB, ?_⟩
  rw [integral_sub hi iB, ← integral_prod _ hj, integral_prod_symm _ hj]
  have he : ∀ᵐ u ∂uniformSphere N,
      (∫ M : Matrix (Fin m) (Fin N) ℝ, dotp (reluV (M.mulVec u)) (h1bar M) ^ 2
        ∂gaussMat m N (2 / (N : ℝ))) =
      (m : ℝ) * (cN N ^ 2 * (2 / (N : ℝ)) ^ 2 * ((N : ℝ) + 2) / 2) +
        (m : ℝ) * ((m : ℝ) - 1) * ((2 / (N : ℝ)) * N * cN N ^ 2) ^ 2 := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    exact (direction_square_rows hN hu (by positivity)).2
  rw [integral_congr_ae he]
  simp_rw [hB]
  rw [integral_const_mul, hQ.2]
  simp only [integral_const, probReal_univ, one_smul]
  field_simp
  ring

end BstLean.Part218
#print axioms BstLean.Part218.worldDirection_mean
