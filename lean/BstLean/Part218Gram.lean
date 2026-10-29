import BstLean.Part218Cubic

/-! The cubic Gaussian Gram estimate uses the covariance trace and Frobenius bound. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part109

lemma nonnegative_cubic_sum {ι : Type} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) {F : ℝ} (hF : 0 ≤ F)
    (h2 : (∑ i, a i ^ 2) ≤ F ^ 2) :
    (∑ i, a i ^ 3) ≤ F ^ 3 := by
  classical
  have hi : ∀ i, a i ≤ F := by
    intro i
    have hh : a i ^ 2 ≤ F ^ 2 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)).trans h2
    exact (sq_le_sq₀ (ha i) hF).mp hh
  calc
    _ ≤ ∑ i, F * a i ^ 2 := Finset.sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_right (hi i) (sq_nonneg (a i))
      nlinarith only [this]
    _ = F * ∑ i, a i ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ F * F ^ 2 := mul_le_mul_of_nonneg_left h2 hF
    _ = _ := by ring

/-- A Frobenius bound supplies the paper's cubic Gaussian estimate. -/
theorem diagonal_cubic_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {T F : ℝ}
    (hT : ∑ i, a i = T) (hF : 0 ≤ F) (h2 : (∑ i, a i ^ 2) ≤ F ^ 2) :
    (∫ x : ι → ℝ, (∑ i, a i * x i ^ 2) ^ 3 ∂stdGauss ι) ≤ (T + 2 * F) ^ 3 := by
  rw [(diagonal_cubic a).2, hT]
  have hT0 : 0 ≤ T := hT ▸ Finset.sum_nonneg (fun i _ => ha i)
  have h3 := nonnegative_cubic_sum a ha hF h2
  have h22 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 6 * T by positivity)
  have hp : 0 ≤ T ^ 2 * F := mul_nonneg (sq_nonneg _) hF
  have hp' : 0 ≤ T * F ^ 2 := mul_nonneg hT0 (sq_nonneg _)
  nlinarith

/-- The bound applies to an actual integral Gram form, with all integrability supplied. -/
theorem gram_cubic_le {ι X : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    {T F : ℝ} (hT : (∑ i, ∫ y, f i y ^ 2 ∂μ) = T) (hF : 0 ≤ F)
    (hFrob : (∑ i, ∑ j, (∫ y, f i y * f j y ∂μ) ^ 2) ≤ F ^ 2) :
    Integrable (fun x : ι → ℝ => (∫ y, (∑ i, x i * f i y) ^ 2 ∂μ) ^ 3)
      (stdGauss ι) ∧
    (∫ x : ι → ℝ, (∫ y, (∑ i, x i * f i y) ^ 2 ∂μ) ^ 3 ∂stdGauss ι) ≤
      (T + 2 * F) ^ 3 := by
  obtain ⟨V, a, hV, ha, hform, htr, htr2⟩ := gram_diag μ f hf
  have hm : Measurable (fun x : ι → ℝ => V.mulVec x) := by fun_prop
  have mp : MeasurePreserving (fun x : ι → ℝ => V.mulVec x) (stdGauss ι) (stdGauss ι) :=
    ⟨hm, stdGauss_map_orth V hV⟩
  have mf : Measurable (fun x : ι → ℝ => (∑ i, a i * x i ^ 2) ^ 3) := by fun_prop
  simp_rw [hform]
  refine ⟨mp.integrable_comp_of_integrable (diagonal_cubic a).1, ?_⟩
  rw [← integral_map hm.aemeasurable mf.aestronglyMeasurable, mp.map_eq]
  exact diagonal_cubic_le a ha (htr.trans hT) hF (htr2 ▸ hFrob)

end BstLean.Part218
#print axioms BstLean.Part218.gram_cubic_le
