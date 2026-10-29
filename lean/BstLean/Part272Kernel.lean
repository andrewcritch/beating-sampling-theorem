import BstLean.Part272Substitution
import BstLean.Part272Coord

/-!
# Part 272: integrability under the scalar substitution

This file supplies an integrability result for the proposed Fubini step.
It does not assert the coordinate-density formula.
-/

namespace BstLean.Part272

open Real MeasureTheory ProbabilityTheory Set

/-- A scalar coordinate divided by a Euclidean length lies in the closed unit interval. -/
theorem scalar_coord_mem (x r : ℝ) : x/√(x^2+r^2) ∈ Icc (-1 : ℝ) 1 := by
  have hq : 0 ≤ x^2+r^2 := by positivity
  have hs : 0 ≤ √(x^2+r^2) := sqrt_nonneg _
  have ha : |x| ≤ √(x^2+r^2) := by
    have hsq := sqrt_sq_eq_abs x
    exact hsq ▸ sqrt_le_sqrt (by nlinarith [sq_nonneg r])
  apply abs_le.mp
  rw [abs_div, abs_of_nonneg hs]
  by_cases h : √(x^2+r^2) = 0
  · simp [h]
  · exact (div_le_one (lt_of_le_of_ne hs (Ne.symm h))).mpr ha

/-- The substitution transfers integrability from the real axis to `(-1,1)`. -/
theorem coordSub_integrable {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) (hf : Integrable f) :
    IntegrableOn (fun z => (r/((1-z^2)*√(1-z^2)))*f (coordSub r z)) (Ioo (-1 : ℝ) 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun z hz => (coordSub_hasDerivAt hr hz).hasDerivWithinAt) (coordSub_injOn hr) f
  rw [coordSub_image hr] at h
  have hi := h.mp (by simpa using hf)
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  have hb := coordSub_base_pos hz
  rw [abs_of_pos (div_pos hr (mul_pos hb (sqrt_pos.mpr hb))), smul_eq_mul]

/-- The Gaussian-weighted bounded scalar integrand is integrable with respect to volume. -/
theorem scalar_weight_integrable (r : ℝ) {g : ℝ → ℝ} (hg : Measurable g)
    (hb : ∃ M, ∀ z ∈ Icc (-1 : ℝ) 1, |g z| ≤ M) :
    Integrable (fun x => gaussianPDFReal 0 1 x * g (x/√(x^2+r^2))) := by
  obtain ⟨M, hM⟩ := hb
  refine ((integrable_gaussianPDFReal 0 1).const_mul M).mono' ?_ ?_
  · exact ((measurable_gaussianPDFReal 0 1).mul
      (hg.comp (measurable_id.div ((measurable_id.pow_const 2).add_const (r^2)).sqrt))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
    calc gaussianPDFReal 0 1 x * |g (x/√(x^2+r^2))| ≤ gaussianPDFReal 0 1 x*M :=
        mul_le_mul_of_nonneg_left (hM _ (scalar_coord_mem x r)) (gaussianPDFReal_nonneg 0 1 x)
      _ = M*gaussianPDFReal 0 1 x := by ring

/-- Each positive-radius slice of the transformed kernel is integrable. -/
theorem coord_kernel_integrable {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ} (hg : Measurable g)
    (hb : ∃ M, ∀ z ∈ Icc (-1 : ℝ) 1, |g z| ≤ M) :
    IntegrableOn (fun z => (r/((1-z^2)*√(1-z^2)))*
      (gaussianPDFReal 0 1 (coordSub r z)*g z)) (Ioo (-1 : ℝ) 1) := by
  have h := coordSub_integrable hr _ (scalar_weight_integrable r hg hb)
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  rw [coordSub_normalize hr hz]

end BstLean.Part272

#print axioms BstLean.Part272.coord_kernel_integrable
