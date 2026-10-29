import BstLean.Part188Weight
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Bounds for the capped reciprocal square root. These bounds include the cap boundary. -/
namespace BstLean.Part229
open Real
open BstLean.Part188

lemma weight_eq_inv_sqrt (a d f : ℝ) :
    weight a d f = (√(max (a - f ^ 2) d))⁻¹ := by
  simp [weight, weightSq, Real.sqrt_inv]

lemma weight_le {a d f : ℝ} (hd : 0 < d) : weight a d f ≤ (√d)⁻¹ := by
  rw [weight_eq_inv_sqrt]
  exact inv_anti₀ (Real.sqrt_pos.mpr hd) (Real.sqrt_le_sqrt (le_max_right _ _))

lemma inv_sqrt_sub_bound {d u v : ℝ} (hd : 0 < d) (hu : d ≤ u) (hv : d ≤ v) :
    |(√u)⁻¹ - (√v)⁻¹| ≤ |u - v| / (d * √d) := by
  have hu0 : 0 < u := hd.trans_le hu
  have hv0 : 0 < v := hd.trans_le hv
  have hsu : 0 < √u := Real.sqrt_pos.mpr hu0
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv0
  have hsd : 0 < √d := Real.sqrt_pos.mpr hd
  have huD : √d ≤ √u := Real.sqrt_le_sqrt hu
  have hvD : √d ≤ √v := Real.sqrt_le_sqrt hv
  have hprod : d ≤ √u * √v := by
    have := mul_le_mul huD hvD hsd.le hsu.le
    rwa [Real.mul_self_sqrt hd.le] at this
  have hden : d * √d ≤ √u * √v * (√u + √v) := by
    have hsum : √d ≤ √u + √v := by linarith
    exact mul_le_mul hprod hsum hsd.le (mul_nonneg hsu.le hsv.le)
  have he : (√u)⁻¹ - (√v)⁻¹ = (v - u) / (√u * √v * (√u + √v)) := by
    field_simp
    nlinarith [Real.sq_sqrt hu0.le, Real.sq_sqrt hv0.le]
  rw [he, abs_div, abs_of_pos (show 0 < √u * √v * (√u + √v) by positivity),
    abs_sub_comm v u]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden

lemma weight_sub_bound {a d f g : ℝ} (hd : 0 < d) :
    |weight a d f - weight a d g| ≤ |f ^ 2 - g ^ 2| / (d * √d) := by
  rw [weight_eq_inv_sqrt, weight_eq_inv_sqrt]
  refine (inv_sqrt_sub_bound hd (le_max_right _ _) (le_max_right _ _)).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := abs_max_sub_max_le_abs (a - f ^ 2) (a - g ^ 2) d
  have he : a - f ^ 2 - (a - g ^ 2) = g ^ 2 - f ^ 2 := by ring
  rwa [he, abs_sub_comm (g ^ 2) (f ^ 2)] at h

lemma weight_sub_bounded {a d f g R : ℝ} (hd : 0 < d)
    (hf : |f| ≤ R) (hg : |g| ≤ R) :
    |weight a d f - weight a d g| ≤ (2 * R / (d * √d)) * |f - g| := by
  have hs : |f + g| ≤ 2 * R := (abs_add_le _ _).trans (by linarith)
  calc
    _ ≤ |f ^ 2 - g ^ 2| / (d * √d) := weight_sub_bound hd
    _ = |f - g| * |f + g| / (d * √d) := by rw [← abs_mul]; congr 2; ring
    _ ≤ |f - g| * (2 * R) / (d * √d) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) (by positivity)
    _ = _ := by ring

lemma weight_continuous (a : ℝ) {d : ℝ} (hd : 0 < d) :
    Continuous (weight a d) := by
  have h : Continuous (fun f : ℝ => (√(max (a - f ^ 2) d))⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro f
      exact (Real.sqrt_pos.mpr (hd.trans_le (le_max_right _ _))).ne'
  have he : weight a d = fun f : ℝ => (√(max (a - f ^ 2) d))⁻¹ :=
    funext (weight_eq_inv_sqrt a d)
  rw [he]
  exact h

end BstLean.Part229
