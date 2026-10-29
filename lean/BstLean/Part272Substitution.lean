import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-!
# Part 272: the scalar substitution for the coordinate density

For fixed positive tail radius `r`, the substitution is
`x = r*z/sqrt(1-z²)`. Its domain is the open interval `(-1,1)`.
-/

namespace BstLean.Part272

open Real MeasureTheory Set
open scoped NNReal

noncomputable def coordSub (r z : ℝ) : ℝ := r*z/√(1-z^2)

lemma coordSub_base_pos {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) : 0 < 1-z^2 := by
  nlinarith [hz.1, hz.2]

/-- The derivative is positive when the tail radius is positive. -/
theorem coordSub_hasDerivAt {r z : ℝ} (hr : 0 < r) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (coordSub r) (r/((1-z^2)*√(1-z^2))) z := by
  have hb := coordSub_base_pos hz
  have hs : √(1-z^2) ≠ 0 := (sqrt_pos.mpr hb).ne'
  have h := (((hasDerivAt_const z r).mul (hasDerivAt_id z)).div
    (((hasDerivAt_const z 1).sub ((hasDerivAt_id z).pow 2)).sqrt hb.ne') hs)
  refine h.congr_deriv ?_
  dsimp
  have hsq := sq_sqrt hb.le
  field_simp [hs, hb.ne']
  simp only [hsq]
  ring

/-- The inverse latitude map cancels the substitution. -/
theorem coordSub_normalize {r z : ℝ} (hr : 0 < r) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    coordSub r z / √((coordSub r z)^2+r^2) = z := by
  have hb := coordSub_base_pos hz
  have hs : 0 < √(1-z^2) := sqrt_pos.mpr hb
  have he : (coordSub r z)^2+r^2 = (r/√(1-z^2))^2 := by
    unfold coordSub
    field_simp
    nlinarith [sq_sqrt hb.le]
  rw [he, sqrt_sq (div_nonneg hr.le hs.le)]
  unfold coordSub
  field_simp

/-- The substitution is injective on its domain. -/
theorem coordSub_injOn {r : ℝ} (hr : 0 < r) : InjOn (coordSub r) (Ioo (-1 : ℝ) 1) := by
  intro z hz w hw he
  have h1 := coordSub_normalize hr hz
  have h2 := coordSub_normalize hr hw
  rw [he] at h1
  exact h1.symm.trans h2

/-- The substitution covers the whole real axis. -/
theorem coordSub_image {r : ℝ} (hr : 0 < r) :
    coordSub r '' Ioo (-1 : ℝ) 1 = univ := by
  apply eq_univ_iff_forall.mpr
  intro x
  have hq : 0 < x^2+r^2 := by nlinarith [sq_nonneg x]
  have hs : 0 < √(x^2+r^2) := sqrt_pos.mpr hq
  have hsq := sq_sqrt hq.le
  let z := x/√(x^2+r^2)
  have hzsq : z^2 < 1 := by
    dsimp [z]
    rw [div_pow, hsq, div_lt_one hq]
    nlinarith
  have hz : z ∈ Ioo (-1 : ℝ) 1 := by constructor <;> nlinarith
  refine ⟨z, hz, ?_⟩
  have he : 1-z^2 = (r/√(x^2+r^2))^2 := by
    dsimp [z]
    field_simp
    nlinarith
  unfold coordSub
  rw [he, sqrt_sq (div_nonneg hr.le hs.le)]
  dsimp [z]
  field_simp

/-- Change of variables on the open interval, before Gaussian weights are introduced. -/
theorem coordSub_integral {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x = ∫ z in Ioo (-1 : ℝ) 1,
      (r/((1-z^2)*√(1-z^2)))*f (coordSub r z) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun z hz => (coordSub_hasDerivAt hr hz).hasDerivWithinAt) (coordSub_injOn hr) f
  rw [coordSub_image hr, Measure.restrict_univ] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro z hz
  have hb := coordSub_base_pos hz
  dsimp only
  rw [abs_of_pos (div_pos hr (mul_pos hb (sqrt_pos.mpr hb))), smul_eq_mul]

/-- A Gaussian coordinate integral after the scalar substitution. -/
theorem coordSub_gaussian {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) :
    ∫ x, g (x/√(x^2+r^2)) ∂ProbabilityTheory.gaussianReal 0 1 =
      ∫ z in Ioo (-1 : ℝ) 1,
        (r/((1-z^2)*√(1-z^2))) *
          (ProbabilityTheory.gaussianPDFReal 0 1 (coordSub r z)*g z) := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  rw [coordSub_integral hr]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro z hz
  dsimp only
  rw [coordSub_normalize hr hz]

end BstLean.Part272

#print axioms BstLean.Part272.coordSub_hasDerivAt
#print axioms BstLean.Part272.coordSub_normalize
