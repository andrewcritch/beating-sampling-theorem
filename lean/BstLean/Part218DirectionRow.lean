import BstLean.Part218WorldStats
import BstLean.Part159Q1

/-! Exact row moments for the directional first-layer statistic. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part105 BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part140 BstLean.Part141 BstLean.Part159

noncomputable def directionRow (N : ℕ) (u r : Fin N → ℝ) : ℝ :=
  relu (dotp r u) * gfun N r

lemma directionRow_measurable {N : ℕ} (hN : 1 ≤ N) (u : Fin N → ℝ) :
    Measurable (directionRow N u) :=
  (measurable_relu.comp (measurable_dotL u)).mul (measurable_gfun hN)

theorem directionRow_square {N : ℕ} (hN : 1 ≤ N) {u : Fin N → ℝ} (hu : normSq u = 1)
    {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun ξ => directionRow N u (√v • ξ) ^ 2) (stdGauss (Fin N)) ∧
    (∫ ξ, directionRow N u (√v • ξ) ^ 2 ∂stdGauss (Fin N)) =
      cN N ^ 2 * v ^ 2 * ((N : ℝ) + 2) / 2 := by
  have he : ∀ ξ : Fin N → ℝ, directionRow N u (√v • ξ) ^ 2 =
      cN N ^ 2 * v ^ 2 * (relu (dotp ξ u) ^ 2 * normSq ξ) := by
    intro ξ
    have hd : dotp (√v • ξ) u = √v * dotp ξ u := by
      unfold dotp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_assoc]
    unfold directionRow
    rw [gfun_eq hN, hd, relu_mul_of_nonneg (sqrt_nonneg _), mul_pow, mul_pow,
      mul_pow, sq_sqrt hv, nrm_sq, normSq_smul, sq_sqrt hv]
    ring
  simp_rw [he]
  refine ⟨(gauss_relu_normSq hN hu).1.const_mul _, ?_⟩
  rw [integral_const_mul]
  simp only [dotp]
  rw [(gauss_relu_normSq hN hu).2]
  ring

theorem directionRow_mean {N : ℕ} (hN : 1 ≤ N) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1)
    {v : ℝ} (hv : 0 ≤ v) :
    (∫ ξ, directionRow N u0 (√v • ξ) ∂stdGauss (Fin N)) = v * N * cN N ^ 2 := by
  have := uniformSphere_isProbability N hN
  let f := directionRow N u0
  have hf : Measurable f := directionRow_measurable hN u0
  have i1 : Integrable (fun ξ => f (√v • ξ)) (stdGauss (Fin N)) :=
    ((memLp_two_iff_integrable_sq (hf.comp (measurable_const_smul _)).aestronglyMeasurable).mpr
      (directionRow_square hN hu0 hv).1).integrable one_le_two
  let H : (Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun p =>
    relu (∑ i, (√v • p.1) i * u0 i) * relu (∑ i, (√v • p.1) i * p.2 i)
  have hHc : Continuous H := by
    dsimp [H]
    unfold relu
    fun_prop
  have hin : ∀ ξ : Fin N → ℝ, ∫ u, H (ξ, u) ∂uniformSphere N = f (√v • ξ) := by
    intro ξ
    simp only [H, f, directionRow, dotp, gfun]
    rw [integral_const_mul]
  have hHi : Integrable H ((stdGauss (Fin N)).prod (uniformSphere N)) := by
    rw [integrable_prod_iff hHc.aestronglyMeasurable]
    constructor
    · exact Filter.Eventually.of_forall fun ξ =>
        sphere_cont_integrable hN (hHc.comp (continuous_const.prodMk continuous_id))
    · have he : (fun ξ : Fin N → ℝ => ∫ u, ‖H (ξ, u)‖ ∂uniformSphere N) =
          fun ξ => f (√v • ξ) := by
        funext ξ
        rw [← hin ξ]
        apply integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        exact Real.norm_of_nonneg (mul_nonneg (relu_nonneg _) (relu_nonneg _))
      rw [he]
      exact i1
  have hsw := integral_prod_symm _ hHi
  rw [integral_prod _ hHi] at hsw
  simp_rw [hin] at hsw
  change (∫ ξ, f (√v • ξ) ∂stdGauss (Fin N)) = _
  rw [hsw]
  have hrow : ∀ᵐ u ∂uniformSphere N, (∫ ξ, H (ξ, u) ∂stdGauss (Fin N)) =
      v / 2 * BstLean.Part130.kappa (dotp u0 u) := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    have h := (rowPair137 (K := N) hv u0 u).2.1
    rw [kernelPhi_eq_psi, psi_unit _ hu0 hu] at h
    exact h.trans (by ring)
  rw [integral_congr_ae hrow, integral_const_mul]
  change v / 2 * q1 u0 = _
  rw [q1_eq hN hu0, q1_eq_cN hN]
  ring

end BstLean.Part218
#print axioms BstLean.Part218.directionRow_square
#print axioms BstLean.Part218.directionRow_mean
