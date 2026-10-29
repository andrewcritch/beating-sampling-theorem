import BstLean.Part214Sixth
import BstLean.Part150Gauss
import BstLean.Part218Gram

/-! The ReLU coupling uses the actual first-layer covariance form. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part105 BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part139 BstLean.Part141 BstLean.Part205 BstLean.Part214

/-- Smoothing changes ReLU by at most the exact Gaussian absolute first moment. -/
theorem smoothing_coupling (s a : ℝ) :
    |relu a - psiS s a| ≤ |s| * √(2 / π) := by
  have h := abs_int_sub_le (μ := gaussianReal 0 1) (integrable_const (relu a))
    (integrable_relu_shift a s) (integrable_abs_gauss.const_mul |s|) (fun z => by
      refine (relu_lip _ _).trans ?_
      rw [show a - (a + s * z) = -(s * z) by ring, abs_neg, abs_mul])
  simpa only [integral_const, probReal_univ, one_smul, integral_const_mul,
    BstLean.Part150.gauss_abs, psiS] using h

/-- The scalar coupling keeps the input distribution fixed. -/
theorem relu_mean_coupling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (mf : Measurable f) (iR : Integrable (fun u => relu (f u)) μ)
    (a s : ℝ) (i2 : Integrable (fun u => (f u - a) ^ 2) μ) :
    |(∫ u, relu (f u) ∂μ) - psiS s a| ≤
      √(∫ u, (f u - a) ^ 2 ∂μ) + |s| * √(2 / π) := by
  obtain ⟨ia, hb⟩ := integral_abs_le_sqrt (mf.sub measurable_const) i2
  have h := abs_int_sub_le iR (integrable_const (relu a)) ia (fun u => relu_lip _ _)
  simp only [integral_const, probReal_univ, one_smul] at h
  calc
    _ ≤ |(∫ u, relu (f u) ∂μ) - relu a| + |relu a - psiS s a| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (h.trans hb) (smoothing_coupling s a)

variable {N m : ℕ}

noncomputable def centeredFirst (M : Matrix (Fin m) (Fin N) ℝ) (i : Fin m)
    (u : Fin N → ℝ) : ℝ := reluV (M.mulVec u) i - h1bar M i

noncomputable def centeredGram (M : Matrix (Fin m) (Fin N) ℝ) (ξ : Fin m → ℝ) : ℝ :=
  ∫ u, (∑ i, ξ i * centeredFirst M i u) ^ 2 ∂uniformSphere N

lemma centeredFirst_continuous (M : Matrix (Fin m) (Fin N) ℝ) (i : Fin m) :
    Continuous (centeredFirst M i) :=
  ((continuous_apply i).comp (continuous_h1_u M)).sub continuous_const

lemma centeredFirst_memLp (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) (i : Fin m) :
    MemLp (centeredFirst M i) 2 (uniformSphere N) := by
  apply (memLp_two_iff_integrable_sq (centeredFirst_continuous M i).measurable.aestronglyMeasurable).mpr
  exact sphere_cont_integrable hN ((centeredFirst_continuous M i).pow 2)

lemma centeredGram_nonneg (M : Matrix (Fin m) (Fin N) ℝ) (ξ : Fin m → ℝ) :
    0 ≤ centeredGram M ξ := integral_nonneg fun _ => sq_nonneg _

lemma centeredGram_measurable (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) :
    Measurable (centeredGram M) := by
  have he : centeredGram M = fun ξ => ∑ i, ∑ j, ξ i * ξ j *
      ∫ u, centeredFirst M i u * centeredFirst M j u ∂uniformSphere N := by
    funext ξ
    exact BstLean.Part109.gram_expand _ _ (centeredFirst_memLp hN M) ξ
  rw [he]
  fun_prop

/-- The paper's pointwise coupling holds for the actual row discrepancy. -/
theorem rowDiscrepancy_coupling (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ)
    (ξ : Fin m → ℝ) :
    |rowDiscrepancy M ξ| ≤ √(centeredGram M ξ) + worldSigma M * √(2 / π) := by
  have := uniformSphere_isProbability N hN
  have hc : Continuous (fun u => dotp ξ (reluV (M.mulVec u))) :=
    continuous_dotp.comp (continuous_const.prodMk (continuous_h1_u M))
  have he : ∀ u, dotp ξ (reluV (M.mulVec u)) - dotp ξ (h1bar M) =
      ∑ i, ξ i * centeredFirst M i u := by
    intro u
    simp only [dotp, centeredFirst, mul_sub, Finset.sum_sub_distrib]
  have h := relu_mean_coupling (uniformSphere N) hc.measurable
    (sphere_cont_integrable hN (continuous_relu.comp hc))
    (dotp ξ (h1bar M)) (worldSigma M)
    (sphere_cont_integrable hN ((hc.sub continuous_const).pow 2))
  simp_rw [he] at h
  have hs : 0 ≤ worldSigma M := by unfold worldSigma sS; positivity
  simpa only [rowDiscrepancy, rowMean, rowInput, rowSmooth, centeredGram, abs_of_nonneg hs] using h

end BstLean.Part218
#print axioms BstLean.Part218.rowDiscrepancy_coupling
