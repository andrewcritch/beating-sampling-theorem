import BstLean.Part218WorldStats

/-! Exact first-layer energy moments supply the input norm-fluctuation mean. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part105 BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part141 BstLean.Part205 BstLean.Part214

theorem firstQ_second {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun M : Matrix (Fin m) (Fin N) ℝ => firstQ M ^ 2)
      (gaussMat m N (2 / (N : ℝ))) ∧
    (∫ M : Matrix (Fin m) (Fin N) ℝ, firstQ M ^ 2 ∂gaussMat m N (2 / (N : ℝ))) =
      (m : ℝ) ^ 2 / (N : ℝ) ^ 2 + 2 * m / (N : ℝ) ^ 3 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  let v : ℝ := 2 / (N : ℝ)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have he : ∀ ξ : Fin N → ℝ, normSq (√v • ξ) = v * normSq ξ := by
    intro ξ; rw [normSq_smul, sq_sqrt hv]
  have i2 : Integrable (fun ξ : Fin N → ℝ => normSq (√v • ξ) ^ 2) (stdGauss (Fin N)) := by
    simp_rw [he, mul_pow]
    exact (gauss_normSq_sq N).1.const_mul _
  obtain ⟨hi, hh⟩ := rows_sum_sq (m := m) v normSq measurable_normSq i2
  have hQ : ∀ M : Matrix (Fin m) (Fin N) ℝ, firstQ M ^ 2 =
      (∑ i, normSq (rowOf i M)) ^ 2 / (4 * (N : ℝ) ^ 2) := by
    intro M
    rw [firstQ_rows hN hm]
    unfold rowS
    ring
  simp_rw [hQ]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div, hh]
  simp_rw [he, mul_pow]
  rw [integral_const_mul, integral_const_mul, (gauss_normSq N).2, (gauss_normSq_sq N).2]
  dsimp [v]
  field_simp
  <;> ring

lemma input_fourth_joint {N m : ℕ} (hN : 1 ≤ N) :
    Integrable (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) =>
      normSq (reluV (p.1.mulVec p.2)) ^ 2)
      ((gaussMat m N (2 / (N : ℝ))).prod (uniformSphere N)) := by
  have := uniformSphere_isProbability N hN
  let P := gaussMat m N (2 / (N : ℝ))
  have hm : Measurable (fun p : (Fin N → ℝ) × Matrix (Fin m) (Fin N) ℝ =>
      normSq (reluV (p.2.mulVec p.1)) ^ 2) := by
    unfold normSq reluV Matrix.mulVec dotProduct relu
    fun_prop
  have hi : Integrable (fun p : (Fin N → ℝ) × Matrix (Fin m) (Fin N) ℝ =>
      normSq (reluV (p.2.mulVec p.1)) ^ 2) ((uniformSphere N).prod P) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun u => (layer_relu_four (by positivity) u).1), ?_⟩
    have hn : ∀ (u : Fin N → ℝ) (M : Matrix (Fin m) (Fin N) ℝ), ‖normSq (reluV (M.mulVec u)) ^ 2‖ = normSq (reluV (M.mulVec u)) ^ 2 :=
      fun u M => Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun u : Fin N → ℝ => ∫ M : Matrix (Fin m) (Fin N) ℝ,
      ‖normSq (reluV (M.mulVec u)) ^ 2‖ ∂gaussMat m N (2 / (N : ℝ))) (uniformSphere N)
    simp_rw [hn, (layer_relu_four (m := m) (v := 2 / (N : ℝ)) (by positivity) _).2]
    exact sphere_cont_integrable hN (continuous_const.mul ((continuous_normSq.const_mul _).pow 2))
  exact hi.swap

lemma input_fourth_mean {N m : ℕ} (hN : 1 ≤ N) :
    (∫ M : Matrix (Fin m) (Fin N) ℝ,
      ∫ u, normSq (reluV (M.mulVec u)) ^ 2 ∂uniformSphere N
      ∂gaussMat m N (2 / (N : ℝ))) = ((m : ℝ) ^ 2 + 5 * m) / (N : ℝ) ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← integral_prod _ (input_fourth_joint (m := m) hN),
    integral_prod_symm _ (input_fourth_joint (m := m) hN)]
  have he : ∀ᵐ u ∂uniformSphere N,
      (∫ M : Matrix (Fin m) (Fin N) ℝ, normSq (reluV (M.mulVec u)) ^ 2
        ∂gaussMat m N (2 / (N : ℝ))) = ((m : ℝ) ^ 2 + 5 * m) / (N : ℝ) ^ 2 := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    have hu' : normSq u = 1 := hu
    rw [(layer_relu_four (m := m) (by positivity) u).2, hu']
    field_simp
    <;> ring
  rw [integral_congr_ae he]
  simp

lemma worldInputVariance_eq {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) :
    worldInputVariance M = (∫ u, normSq (reluV (M.mulVec u)) ^ 2 ∂uniformSphere N) - firstQ M ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hc : Continuous (fun u : Fin N → ℝ => normSq (reluV (M.mulVec u))) :=
    continuous_normSq.comp (continuous_h1_u M)
  have h := (integral_sq_sub_const (sphere_cont_integrable hN hc)
    (sphere_cont_integrable hN (hc.pow 2)) (firstQ M)).2
  change worldInputVariance M = _ at h
  change worldInputVariance M = _ - 2 * firstQ M * firstQ M + firstQ M ^ 2 at h
  linarith

/-- The actual input norm variance has exactly the paper's expectation `E_V`. -/
theorem worldInputVariance_mean {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (worldInputVariance (N := N) (m := m)) (gaussMat m N (2 / (N : ℝ))) ∧
    (∫ M : Matrix (Fin m) (Fin N) ℝ, worldInputVariance M ∂gaussMat m N (2 / (N : ℝ))) =
      5 * (m : ℝ) / (N : ℝ) ^ 2 - 2 * m / (N : ℝ) ^ 3 := by
  have hi := (input_fourth_joint (m := m) hN).integral_prod_left
  have hQ := firstQ_second hN hm
  have he : worldInputVariance (N := N) (m := m) = fun M =>
      (∫ u, normSq (reluV (M.mulVec u)) ^ 2 ∂uniformSphere N) - firstQ M ^ 2 := by
    funext M; exact worldInputVariance_eq hN M
  rw [he]
  refine ⟨hi.sub hQ.1, ?_⟩
  rw [integral_sub hi hQ.1, input_fourth_mean hN, hQ.2]
  ring

end BstLean.Part218
#print axioms BstLean.Part218.worldInputVariance_mean
