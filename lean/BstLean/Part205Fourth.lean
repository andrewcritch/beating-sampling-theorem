import BstLean.Part205Row

/-! Fourth-moment integrability for the conditional row discrepancy. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part105 BstLean.Part130 BstLean.Part133 BstLean.Part137

lemma fourth_sub_le (x y : ℝ) : (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h : (x - y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x + y)]
  have h' := (sq_le_sq₀ (sq_nonneg (x - y))
    (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg x) (sq_nonneg y)))).mpr h
  nlinarith [h', sq_nonneg (x ^ 2 - y ^ 2)]

lemma rowMean_four_integrable {N m : ℕ} (g : (Fin N → ℝ) → Fin m → ℝ)
    (hN : 1 ≤ N) (hg : Continuous g) :
    Integrable (fun ξ => rowMean g ξ ^ 4) (stdGauss (Fin m)) := by
  have := uniformSphere_isProbability N hN
  let Q : ℝ := ∫ u, normSq (g u) ∂uniformSphere N
  have hQ : 0 ≤ Q := integral_nonneg fun _ => normSq_nonneg _
  have iQ := sphere_cont_integrable hN (continuous_normSq.comp hg)
  have hbound : ∀ ξ, rowMean g ξ ^ 2 ≤ normSq ξ * Q := by
    intro ξ
    have hr : Integrable (fun u => rowInput g ξ u ^ 2) (uniformSphere N) :=
      sphere_cont_integrable hN
        (((rowInput_continuous g hg).comp (continuous_const.prodMk continuous_id)).pow 2)
    refine (sq_integral_le hr).trans ?_
    rw [← integral_const_mul]
    exact integral_mono hr (iQ.const_mul _) fun u =>
      (relu_sq_le _).trans (by simpa [dotp] using dotL_sq_le ξ (g u))
  refine Integrable.mono' ((gauss_normSq_sq m).1.mul_const (Q ^ 2))
    ((rowMean_measurable g hg).pow_const 4).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ξ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := (sq_le_sq₀ (sq_nonneg (rowMean g ξ))
    (mul_nonneg (normSq_nonneg ξ) hQ)).mpr (hbound ξ)
  simpa only [mul_pow, ← pow_mul, show (2 * 2 : ℕ) = 4 from rfl] using h

lemma rowSmooth_four_integrable {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) :
    Integrable (fun ξ => rowSmooth h σ ξ ^ 4) (stdGauss (Fin m)) := by
  have hi := (BstLean.Part140.sq_row (by norm_num : (0 : ℝ) < 1) σ h).2.2.1
  simpa [BstLean.Part140.fQ, rowSmooth, dotp, ← pow_mul] using hi

theorem row_distance_four_integrable {N m : ℕ} (g : (Fin N → ℝ) → Fin m → ℝ)
    (hN : 1 ≤ N) (hg : Continuous g) (h : Fin m → ℝ) (σ : ℝ) :
    Integrable (fun ξ => (rowMean g ξ - rowSmooth h σ ξ) ^ 4) (stdGauss (Fin m)) := by
  have hm : Measurable (rowSmooth h σ) := measurable_psiS.comp
    (measurable_const.prodMk
      ((continuous_dotp.comp (continuous_id.prodMk continuous_const)).measurable))
  refine Integrable.mono' (((rowMean_four_integrable g hN hg).add
    (rowSmooth_four_integrable h σ)).const_mul 8)
    (((rowMean_measurable g hg).sub hm).pow_const 4).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ξ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact fourth_sub_le _ _

end BstLean.Part205

#print axioms BstLean.Part205.row_distance_four_integrable
