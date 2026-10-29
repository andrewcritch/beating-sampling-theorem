import BstLean.Part45Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace BstLean.Part45
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private lemma abs_kernel_integrable (s : ℝ) (hs : -1 < s) :
    Integrable (fun x : ℝ => |x| ^ s * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
  have hp : IntegrableOn (fun x : ℝ => |x| ^ s * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) hs).congr_fun
      (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  rw [← integrableOn_univ, ← @Iio_union_Ici ℝ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iio, neg_zero] using hp

private lemma abs_kernel_half_integral (r : ℝ) (hr : r < 1 / 2) :
    (∫ x : ℝ in Ioi 0, x ^ (-2 * r) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
      (2 : ℝ) ^ (1 / 2 - r) * Real.Gamma (1 / 2 - r) / 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (show 0 < 1 / 2 - r by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← integral_comp_rpow_Ioi_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  have heq : (∫ x : ℝ in Ioi 0,
      (2 * x ^ ((2 : ℝ) - 1)) •
      ((x ^ (2 : ℝ)) ^ (1 / 2 - r - 1) * Real.exp (-(1 / 2 * x ^ (2 : ℝ))))) =
      2 * ∫ x : ℝ in Ioi 0, x ^ (-2 * r) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [smul_eq_mul, ← Real.rpow_mul hx.le, Real.rpow_two]
    have hexp : (2 : ℝ) * (1 / 2 - r - 1) = -2 * r - 1 := by ring
    rw [hexp, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    simp only [neg_mul]
    have hp : x * x ^ (-2 * r - 1) = x ^ (-2 * r) := by
      nth_rw 1 [← Real.rpow_one x]
      rw [← Real.rpow_add hx]
      congr 1
      ring
    calc
      _ = 2 * (x * x ^ (-2 * r - 1)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by ring
      _ = _ := by rw [hp]; ring
  rw [heq] at h
  norm_num only [one_div_one_div] at h
  linarith

lemma scalar_negmom (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2) :
    ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ^ (-r) ∂gaussianReal 0 1 = ENNReal.ofReal (mr r) := by
  let f : ℝ → ℝ := fun x => |x| ^ (-2 * r)
  have hk := abs_kernel_integrable (-2 * r) (by linarith)
  have hd : (fun x : ℝ => gaussianPDFReal 0 1 x * f x) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| ^ (-2 * r) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    ext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, f]
    rw [show (-x ^ 2 / (2 : ℝ)) = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  have hf : Integrable f (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
    apply (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)).2
    simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      smul_eq_mul, hd] using hk.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have he : ∫ x, f x ∂gaussianReal 0 1 = mr r := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
    simp only [smul_eq_mul]
    rw [hd, integral_const_mul]
    have habs : (∫ x : ℝ, |x| ^ (-2 * r) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
        2 * ∫ x : ℝ in Ioi 0, x ^ (-2 * r) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
      convert integral_comp_abs (f := fun x : ℝ => x ^ (-2 * r) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) using 1
      simp
    rw [habs, abs_kernel_half_integral r hr1]
    unfold mr
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow,
      show (1 / 2 - r : ℝ) = 1 / 2 + -r by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp
  rw [← he, ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg x) _)]
  apply lintegral_congr_ae
  have hn : ∀ᵐ x : ℝ ∂gaussianReal 0 1, x ≠ 0 := by
    letI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (by norm_num : (1 : NNReal) ≠ 0)
    simpa using (measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℝ)))
  filter_upwards [hn] with x hx
  rw [ENNReal.ofReal_rpow_of_pos (sq_pos_of_ne_zero hx)]
  congr 1
  dsimp [f]
  rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg x)]
  congr 1
  ring

lemma convexOn_neg_rpow (r : ℝ) (hr : 0 < r) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ (-r)) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
  · exact fun x hx => (Real.continuousAt_rpow_const x (-r) (Or.inl (ne_of_gt hx))).continuousWithinAt
  · intro x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (interior_subset hx)))).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [(Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (interior_subset hx)))).deriv,
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (interior_subset hy)))).deriv]
    apply mul_le_mul_of_nonpos_left _ (by linarith : -r ≤ 0)
    exact Real.rpow_le_rpow_of_nonpos (interior_subset hx) hxy (by linarith)

end BstLean.Part45
