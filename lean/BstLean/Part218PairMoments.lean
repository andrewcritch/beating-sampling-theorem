import BstLean.Part214Pair

/-! Concrete Gaussian shared-row moments for the first-layer Wishart statistics. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part214

lemma centered_product_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (iX : Integrable X μ) (iY : Integrable Y μ)
    (iXY : Integrable (fun x => X x * Y x) μ) (a b : ℝ) :
    Integrable (fun x => (X x - a) * (Y x - b)) μ ∧
    (∫ x, (X x - a) * (Y x - b) ∂μ) =
      (∫ x, X x * Y x ∂μ) - b * (∫ x, X x ∂μ) - a * (∫ x, Y x ∂μ) + a * b := by
  have he : (fun x => (X x - a) * (Y x - b)) =
      fun x => X x * Y x - b * X x - a * Y x + a * b := by funext x; ring
  rw [he]
  refine ⟨((iXY.sub (iX.const_mul b)).sub (iY.const_mul a)).add (integrable_const _), ?_⟩
  have iA : Integrable (fun x => X x * Y x - b * X x) μ := iXY.sub (iX.const_mul b)
  have iB : Integrable (fun x => X x * Y x - b * X x - a * Y x) μ := iA.sub (iY.const_mul a)
  rw [integral_add iB (integrable_const _),
    integral_sub iA (iY.const_mul a),
    integral_sub iXY (iX.const_mul b), integral_const_mul, integral_const_mul]
  simp

theorem pair_radial_moment {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      normSq p.1 ^ k * dotp p.2 p.1 ^ 2) ((stdGauss (Fin N)).prod (stdGauss (Fin N))) ∧
    (∫ p : (Fin N → ℝ) × (Fin N → ℝ), normSq p.1 ^ k * dotp p.2 p.1 ^ 2
      ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) = BstLean.Part36.rhoD N (k + 1) := by
  have hm : Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      normSq p.1 ^ k * dotp p.2 p.1 ^ 2) :=
    ((measurable_normSq.comp measurable_fst).pow_const k).mul
      ((continuous_dotp.measurable.comp (measurable_snd.prodMk measurable_fst)).pow_const 2)
  have he : ∀ x : Fin N → ℝ, (∫ y, normSq x ^ k * dotp y x ^ 2 ∂stdGauss (Fin N)) =
      normSq x ^ (k + 1) := by
    intro x
    rw [integral_const_mul, (pair_dot_two N x).2, pow_succ]
  have hi : Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      normSq p.1 ^ k * dotp p.2 p.1 ^ 2) ((stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun x => ?_), ?_⟩
    · simpa only [] using (pair_dot_two N x).1.const_mul (normSq x ^ k)
    · have hn : ∀ x y : Fin N → ℝ, ‖normSq x ^ k * dotp y x ^ 2‖ =
          normSq x ^ k * dotp y x ^ 2 := by
        intro x y
        exact Real.norm_of_nonneg (mul_nonneg (pow_nonneg (normSq_nonneg _) _) (sq_nonneg _))
      simp_rw [hn, he]
      exact gaussian_normSq_pow_integrable hN _
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  simp_rw [he]
  exact gaussian_normSq_pow N (k + 1)

/-- A pair kernel and the diagonal statistic at one endpoint have covariance `4N(N+2)`. -/
theorem pair_diagonal_covariance {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      (dotp p.2 p.1 ^ 2 - N) * (normSq p.1 ^ 2 - (N : ℝ) * (N + 2)))
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) ∧
    (∫ p : (Fin N → ℝ) × (Fin N → ℝ),
      (dotp p.2 p.1 ^ 2 - N) * (normSq p.1 ^ 2 - (N : ℝ) * (N + 2))
      ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) = 4 * (N : ℝ) * (N + 2) := by
  have iy : Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => normSq p.1 ^ 2)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) :=
    (gaussian_normSq_pow_integrable hN 2).comp_fst (stdGauss (Fin N))
  have ip : Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => dotp p.2 p.1 ^ 2 * normSq p.1 ^ 2)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
    simpa only [mul_comm] using (pair_radial_moment hN 2).1
  obtain ⟨hi, he⟩ := centered_product_integral (pair_kernel_moments N).1 iy ip
    (N : ℝ) ((N : ℝ) * (N + 2))
  refine ⟨hi, ?_⟩
  rw [he, (pair_kernel_moments N).2.1]
  have ep : (∫ p : (Fin N → ℝ) × (Fin N → ℝ), dotp p.2 p.1 ^ 2 * normSq p.1 ^ 2
      ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) = BstLean.Part36.rhoD N 3 := by
    simpa only [mul_comm] using (pair_radial_moment hN 2).2
  rw [ep, integral_prod _ iy]
  simp only [integral_const, probReal_univ, one_smul]
  rw [gaussian_normSq_pow]
  simp [BstLean.Part36.rhoD, Finset.prod_range_succ]
  ring

/-- The raw product of two pair kernels that share one Gaussian row. -/
theorem shared_pair_raw {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun p : (Fin N → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      dotp p.2.1 p.1 ^ 2 * dotp p.2.2 p.1 ^ 2)
      ((stdGauss (Fin N)).prod ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) ∧
    (∫ p : (Fin N → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)),
      dotp p.2.1 p.1 ^ 2 * dotp p.2.2 p.1 ^ 2
      ∂(stdGauss (Fin N)).prod ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) =
      (N : ℝ) * (N + 2) := by
  let μ := stdGauss (Fin N)
  let H := fun p : (Fin N → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
    dotp p.2.1 p.1 ^ 2 * dotp p.2.2 p.1 ^ 2
  have hm : Measurable H := by
    unfold H dotp
    fun_prop
  have hs : ∀ x, Integrable (fun p => H (x, p)) (μ.prod μ) := fun x =>
    (pair_dot_two N x).1.mul_prod (pair_dot_two N x).1
  have he : ∀ x, (∫ p, H (x, p) ∂μ.prod μ) = normSq x ^ 2 := by
    intro x
    dsimp [H, μ]
    rw [integral_prod_mul (fun y : Fin N → ℝ => dotp y x ^ 2)
      (fun z : Fin N → ℝ => dotp z x ^ 2), (pair_dot_two N x).2, pow_two]
  have hi : Integrable H (μ.prod (μ.prod μ)) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hs, ?_⟩
    have hn : ∀ p, ‖H p‖ = H p := fun p => Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    simp_rw [hn, he]
    exact gaussian_normSq_pow_integrable hN 2
  refine ⟨hi, ?_⟩
  change (∫ p, H p ∂μ.prod (μ.prod μ)) = _
  rw [integral_prod _ hi]
  simp_rw [he]
  change (∫ x, normSq x ^ 2 ∂stdGauss (Fin N)) = _
  rw [(BstLean.Part137.gauss_normSq_sq N).2]
  ring

end BstLean.Part218
#print axioms BstLean.Part218.pair_diagonal_covariance
#print axioms BstLean.Part218.shared_pair_raw
