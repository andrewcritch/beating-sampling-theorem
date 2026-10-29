import BstLean.Part209Kernel
import BstLean.Part151J2
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation under the Gaussian row integral. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Filter Topology Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part29 (stdGauss)
open BstLean.Part151 (mask measurable_mask)

variable {d : ℕ}

lemma measurable_dot_left (a : Fin d → ℝ) : Measurable (fun w => dotp w a) := by
  unfold dotp
  fun_prop

lemma abs_dot_product_le (w a b : Fin d → ℝ) :
    |dotp w a| * |dotp w b| ≤ normSq w * (nrm a * nrm b) := by
  calc |dotp w a| * |dotp w b| ≤ (nrm w * nrm a) * (nrm w * nrm b) :=
      mul_le_mul (abs_dot_le w a) (abs_dot_le w b) (abs_nonneg _)
        (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
    _ = _ := by rw [← nrm_sq w]; ring

lemma row_pair_integrable (a b : Fin d → ℝ) :
    Integrable (fun w => relu (dotp w a) * relu (dotp w b)) (stdGauss (Fin d)) := by
  apply ((BstLean.Part149.stdGauss_normSq d).1.mul_const (nrm a * nrm b)).mono'
  · exact ((measurable_relu.comp (measurable_dot_left a)).mul
      (measurable_relu.comp (measurable_dot_left b))).aestronglyMeasurable
  · exact ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (abs_relu_le _) (abs_relu_le _) (abs_nonneg _) (abs_nonneg _)).trans
        (abs_dot_product_le w a b)

lemma hasDerivAt_relu_ne {z : ℝ} (hz : z ≠ 0) : HasDerivAt relu (mask z) z := by
  rcases lt_or_gt_of_ne hz with hz | hz
  · rw [BstLean.Part151.mask_of_nonpos hz.le]
    apply (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hz] with y hy
    exact relu_of_nonpos hy.le
  · rw [BstLean.Part151.mask_of_pos hz]
    apply (hasDerivAt_id z).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hz] with y hy
    exact relu_of_nonneg hy.le

lemma relu_abs_sub_le (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  rw [max_comm 0 a, max_comm 0 b]
  exact abs_max_sub_max_le_abs a b 0

lemma dot_line (w a u : Fin d → ℝ) (t : ℝ) :
    dotp w (a + t • u) = dotp w a + t * dotp w u := by
  simp only [dotp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intros
  ring

/-- The integrable domination is independent of the perturbation parameter. -/
lemma row_pair_lipschitz (w a b u : Fin d → ℝ) :
    LipschitzWith (Real.nnabs (normSq w * (nrm u * nrm b)))
      (fun t : ℝ => relu (dotp w (a + t • u)) * relu (dotp w b)) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  simp only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg
    (mul_nonneg (normSq_nonneg w) (mul_nonneg (nrm_nonneg u) (nrm_nonneg b)))]
  rw [← sub_mul, abs_mul]
  calc |relu (dotp w (a + t • u)) - relu (dotp w (a + s • u))| * |relu (dotp w b)|
      ≤ |dotp w (a + t • u) - dotp w (a + s • u)| * |dotp w b| :=
        mul_le_mul (relu_abs_sub_le _ _) (abs_relu_le _) (abs_nonneg _) (abs_nonneg _)
    _ = (|dotp w u| * |dotp w b|) * |t - s| := by
      rw [dot_line, dot_line, show dotp w a + t * dotp w u -
        (dotp w a + s * dotp w u) = (t - s) * dotp w u by ring, abs_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (abs_dot_product_le w u b) (abs_nonneg _)

/-- The row derivative passes through the integral at each fixed nonzero first vector. -/
theorem row_pair_derivative_integral {a : Fin d → ℝ} (ha : a ≠ 0) (b u : Fin d → ℝ) :
    Integrable (fun w => mask (dotp w a) * dotp w u * relu (dotp w b)) (stdGauss (Fin d)) ∧
    HasDerivAt (fun t : ℝ => ∫ w, relu (dotp w (a + t • u)) * relu (dotp w b)
      ∂stdGauss (Fin d))
      (∫ w, mask (dotp w a) * dotp w u * relu (dotp w b) ∂stdGauss (Fin d)) 0 := by
  apply hasDerivAt_integral_of_dominated_loc_of_lip (s := Set.univ)
    (bound := fun w => normSq w * (nrm u * nrm b)) (by simp)
  · exact Filter.Eventually.of_forall fun t => ((measurable_relu.comp (measurable_dot_left (a + t • u))).mul
      (measurable_relu.comp (measurable_dot_left b))).aestronglyMeasurable
  · simpa using row_pair_integrable a b
  · exact (((measurable_mask.comp (measurable_dot_left a)).mul (measurable_dot_left u)).mul
      (measurable_relu.comp (measurable_dot_left b))).aestronglyMeasurable
  · exact ae_of_all _ fun w => (row_pair_lipschitz w a b u).lipschitzOnWith
  · exact (BstLean.Part149.stdGauss_normSq d).1.mul_const _
  · filter_upwards [BstLean.Part151.ae_dot_ne ha] with w hw
    have hd : HasDerivAt (fun t : ℝ => dotp w (a + t • u)) (dotp w u) 0 := by
      simp_rw [dot_line]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotp w u)).const_add (dotp w a)
    have hz : dotp w (a + (0 : ℝ) • u) ≠ 0 := by
      simpa only [dotp, dotProduct, zero_smul, add_zero] using hw
    have h := ((hasDerivAt_relu_ne hz).comp 0 hd).mul_const (relu (dotp w b))
    simpa using h

/-- The exact Gaussian gated-row mean, with all nonzero parallel cases included. -/
theorem row_pair_mean {a : Fin d → ℝ} (ha : a ≠ 0) (b u : Fin d → ℝ) :
    (∫ w, mask (dotp w a) * dotp w u * relu (dotp w b) ∂stdGauss (Fin d)) =
      dotp (kernelVector a b) u / 2 := by
  have h := (row_pair_derivative_integral ha b u).2
  have he : (fun t : ℝ => ∫ w, relu (dotp w (a + t • u)) * relu (dotp w b)
      ∂stdGauss (Fin d)) = fun t => kernelPhi (a + t • u) b / 2 := by
    funext t
    have h := row_formula_std (a + t • u) b
    change 2 * (∫ w, relu (dotp w (a + t • u)) * relu (dotp w b) ∂stdGauss (Fin d)) =
      kernelPhi (a + t • u) b at h
    linarith
  rw [he] at h
  exact h.unique ((hasDerivAt_kernelPhi_line ha u).div_const 2)

end BstLean.Part209
