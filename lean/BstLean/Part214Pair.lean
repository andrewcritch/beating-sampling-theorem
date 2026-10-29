import BstLean.Part214Diagonal

/-! Exact two-row Gaussian moments for the off-diagonal Wishart kernel. -/
namespace BstLean.Part214
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137

lemma pair_dot_two (N : ℕ) (x : Fin N → ℝ) :
    Integrable (fun y => dotp y x ^ 2) (stdGauss (Fin N)) ∧
    (∫ y, dotp y x ^ 2 ∂stdGauss (Fin N)) = normSq x := by
  simpa using row_two (by norm_num : (0 : ℝ) ≤ 1) x

lemma pair_dot_four (N : ℕ) (x : Fin N → ℝ) :
    Integrable (fun y => dotp y x ^ 4) (stdGauss (Fin N)) ∧
    (∫ y, dotp y x ^ 4 ∂stdGauss (Fin N)) = 3 * normSq x ^ 2 := by
  simpa using row_four (by norm_num : (0 : ℝ) ≤ 1) x

/-- Independent Gaussian rows have dot-square mean `N` and dot-fourth mean `3N(N+2)`. -/
theorem pair_kernel_moments (N : ℕ) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => dotp p.2 p.1 ^ 2)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) ∧
    (∫ p, dotp p.2 p.1 ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) = N ∧
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => dotp p.2 p.1 ^ 4)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) ∧
    (∫ p, dotp p.2 p.1 ^ 4 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) =
      3 * (N : ℝ) * (N + 2) := by
  have mD : Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => dotp p.2 p.1) :=
    continuous_dotp.measurable.comp (measurable_snd.prodMk measurable_fst)
  have i2 : Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => dotp p.2 p.1 ^ 2)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
    rw [integrable_prod_iff (mD.pow_const 2).aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => (pair_dot_two N x).1, ?_⟩
    have he : ∀ x y : Fin N → ℝ, ‖dotp y x ^ 2‖ = dotp y x ^ 2 := by
      intro x y
      exact Real.norm_of_nonneg (sq_nonneg _)
    simp_rw [he, (pair_dot_two N _).2]
    exact (gauss_normSq N).1
  have i4 : Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => dotp p.2 p.1 ^ 4)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
    rw [integrable_prod_iff (mD.pow_const 4).aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => (pair_dot_four N x).1, ?_⟩
    have he : ∀ x y : Fin N → ℝ, ‖dotp y x ^ 4‖ = dotp y x ^ 4 := by
      intro x y
      exact Real.norm_of_nonneg (by positivity)
    simp_rw [he, (pair_dot_four N _).2]
    exact (gauss_normSq_sq N).1.const_mul 3
  refine ⟨i2, ?_, i4, ?_⟩
  · rw [integral_prod _ i2]
    simp_rw [(pair_dot_two N _).2]
    exact (gauss_normSq N).2
  · rw [integral_prod _ i4]
    simp_rw [(pair_dot_four N _).2]
    rw [integral_const_mul, (gauss_normSq_sq N).2]
    ring

/-- The off-diagonal kernel has variance `2N²+6N`. -/
theorem pair_kernel_variance (N : ℕ) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (dotp p.2 p.1 ^ 2 - N) ^ 2)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) ∧
    (∫ p, (dotp p.2 p.1 ^ 2 - N) ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) =
      2 * (N : ℝ) ^ 2 + 6 * N := by
  obtain ⟨i2, e2, i4, e4⟩ := pair_kernel_moments N
  obtain ⟨hi, he⟩ := integral_sq_sub_const i2
    (by simpa only [← pow_mul] using i4) (N : ℝ)
  refine ⟨hi, ?_⟩
  simp only [← pow_mul] at he
  rw [he, e2, e4]
  ring

/-- The conditional pair mean has variance `2N`, with the shared row retained. -/
theorem pair_conditional_variance (N : ℕ) :
    Integrable (fun x : Fin N → ℝ =>
      ((∫ y, dotp y x ^ 2 ∂stdGauss (Fin N)) - N) ^ 2) (stdGauss (Fin N)) ∧
    (∫ x : Fin N → ℝ, ((∫ y, dotp y x ^ 2 ∂stdGauss (Fin N)) - N) ^ 2
      ∂stdGauss (Fin N)) = 2 * N := by
  simp_rw [(pair_dot_two N _).2]
  obtain ⟨hi, he⟩ := integral_sq_sub_const (gauss_normSq N).1 (gauss_normSq_sq N).1 (N : ℝ)
  refine ⟨hi, ?_⟩
  rw [he, (gauss_normSq N).2, (gauss_normSq_sq N).2]
  ring

end BstLean.Part214
#print axioms BstLean.Part214.pair_kernel_moments
#print axioms BstLean.Part214.pair_kernel_variance
#print axioms BstLean.Part214.pair_conditional_variance
