import BstLean.Part203Composition
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Part 203: exact logarithmic endpoint scaling with explicit domains. -/
namespace BstLean.Part203
open Real

/-- Concavity gives scaling for either sign; positivity is an explicit premise. -/
lemma log_scale {x t : ℝ} (ht : 1 ≤ t) (hx : 0 < 1 + t * x) :
    log (1 + t * x) ≤ t * log (1 + x) := by
  have ht0 : 0 < t := by linarith
  have ha : 0 ≤ 1 / t := by positivity
  have hb : 0 ≤ 1 - 1 / t := by
    have := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ht)
    have hh : 1 / t ≤ (1 : ℝ) := by simpa using this
    linarith
  have h := strictConcaveOn_log_Ioi.concaveOn.2 hx (by norm_num : (0 : ℝ) < 1)
    ha hb (by ring : 1 / t + (1 - 1 / t) = 1)
  have he : 1 / t * (1 + t * x) + (1 - 1 / t) * 1 = 1 + x := by
    field_simp
    ring
  simp only [smul_eq_mul, log_one, mul_zero, add_zero, he] at h
  have hh := mul_le_mul_of_nonneg_left h ht0.le
  have hi : t * (1 / t * log (1 + t * x)) = log (1 + t * x) := by field_simp
  rwa [hi] at hh

lemma log_product_scale {w W X X₀ t : ℝ} (ht : 1 ≤ t)
    (hdom : 0 < 1 + w * X) (hprod : w * X ≤ t * (W * X₀)) :
    log (1 + w * X) ≤ t * log (1 + W * X₀) := by
  have hd : 0 < 1 + t * (W * X₀) := by linarith
  exact (log_le_log hdom (by linarith)).trans (log_scale ht hd)

/-- This common comparison includes the exact logarithm and the free tangent constants. -/
lemma exact_scale {C K β β₀ w w₀ α α₀ L t : ℝ}
    (hC : 0 ≤ C) (hL : 0 < L) (ht : 1 ≤ t)
    (hβ : K * β ≤ t * (K * β₀))
    (hdom : 0 < 1 + w * (exp (L * K * α) - 1))
    (hprod : w * (exp (L * K * α) - 1) ≤
      t * (w₀ * (exp (L * K * α₀) - 1))) :
    exactRhs C K α β w L ≤ t * exactRhs C K α₀ β₀ w₀ L := by
  have hl := div_le_div_of_nonneg_right (log_product_scale ht hdom hprod) hL.le
  rw [mul_div_assoc] at hl
  have hc : C ≤ t * C := by nlinarith
  unfold exactRhs
  nlinarith

lemma tg_scale {C K β β₀ w w₀ α α₀ L t u₀ : ℝ}
    (hC : 0 ≤ C) (hL : 0 < L) (hu : -1 < u₀) (ht : 1 ≤ t)
    (hβ : K * β ≤ t * (K * β₀))
    (hprod : w * (exp (L * K * α) - 1) ≤
      t * (w₀ * (exp (L * K * α₀) - 1))) :
    tgRhs C K α β w L u₀ ≤ t * tgRhs C K α₀ β₀ w₀ L u₀ := by
  have hk := tangentC_nonneg hu hL
  have hc : C + tangentC u₀ L ≤ t * (C + tangentC u₀ L) := by nlinarith
  have hl := div_le_div_of_nonneg_right hprod
    (mul_nonneg hL.le (by linarith : 0 ≤ 1 + u₀))
  have hl' : w * (exp (L * K * α) - 1) / (L * (1 + u₀)) ≤
      t * (w₀ * (exp (L * K * α₀) - 1) / (L * (1 + u₀))) := by
    simpa only [mul_div_assoc] using hl
  unfold tgRhs
  nlinarith only [hc, hβ, hl']

lemma radius_sub_scale {x h t : ℝ} (hh : 0 ≤ h) (hx : 2 * h ≤ x) (ht : 1 ≤ t) :
    t * x - h ≤ t ^ 2 * (x - h) := by
  have h1 : 0 ≤ (t - 1) * (t * x - (t + 1) * h) := by
    apply mul_nonneg (by linarith)
    nlinarith
  nlinarith

/-- The negative free-tangent constant scales only under the stronger root guard. -/
lemma negative_beta_scale {H b h x t : ℝ} (hH : 0 ≤ H) (hb : 0 < b)
    (hh : 0 ≤ h) (hx : 2 * h + 2 * H / b ≤ x) (ht : 1 ≤ t) :
    t ^ 2 * (-H * (b * (x - h)) + H ^ 2) ≤
      -H * (b * (t * x - h)) + H ^ 2 := by
  have hd : 0 ≤ H / b := div_nonneg hH hb.le
  rw [mul_div_assoc] at hx
  have hs := radius_sub_scale (x := x) (t := t) (h := h + H / b)
    (by linarith) (by linarith) ht
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hH hb.le)
  have he1 : H * b * (t * x - (h + H / b)) =
      H * b * (t * x - h) - H ^ 2 := by field_simp; ring
  have he2 : H * b * (t ^ 2 * (x - (h + H / b))) =
      t ^ 2 * (H * b * (x - h) - H ^ 2) := by field_simp; ring
  rw [he1, he2] at hm
  nlinarith only [hm]

/-- A negative failure threshold is in the bounded interval used by END. -/
lemma negative_admissible {a h Q z : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hz : z = a * (√Q + h) ^ 2 / 10) (hz0 : 1 / 1000 ≤ z) :
    1 / 1000 ≤ z ∧ z ≤ a * (1 + h) ^ 2 / 10 ∧
      (√(10 * z / a) - h) ^ 2 = Q ∧ (√(10 * z / a) - h) ^ 2 ≤ 1 := by
  have hsq : √Q ≤ 1 := by
    have := Real.sqrt_le_sqrt hQ1
    simpa using this
  have he : 10 * z / a = (√Q + h) ^ 2 := by rw [hz]; field_simp
  have he2 : √(10 * z / a) = √Q + h := by
    rw [he, Real.sqrt_sq (by positivity)]
  have he3 : (√(10 * z / a) - h) ^ 2 = Q := by
    rw [he2, add_sub_cancel_right, Real.sq_sqrt hQ0]
  refine ⟨hz0, ?_, he3, by rwa [he3]⟩
  rw [hz]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 2) ha.le)
    (by norm_num)

/-- Overcoverage on sampling success lies inside the admissible negative END interval. -/
theorem negative_failure_admissible {p R Q a h : ℝ}
    (hR : 0 ≤ R) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (ha : 0 < a) (hh : 0 ≤ h)
    (hRQ : |√R - √Q| ≤ h)
    (hfail : ¬ BstLean.Part156.outRule a R ≤ max (10 * p) (1 / 100)) :
    p < BstLean.Part156.zminus a h Q ∧
      1 / 1000 < BstLean.Part156.zminus a h Q ∧
      BstLean.Part156.zminus a h Q ≤ a * (1 + h) ^ 2 / 10 ∧
      (√(10 * BstLean.Part156.zminus a h Q / a) - h) ^ 2 ≤ 1 := by
  have hf := BstLean.Part156.not_outRule_le hR ha hRQ hfail
  have hd := negative_admissible ha hh hQ0 hQ1
    (z := BstLean.Part156.zminus a h Q)
    (by unfold BstLean.Part156.zminus; ring) hf.2.2.le
  exact ⟨hf.2.1, hf.2.2, hd.2.1, hd.2.2.2⟩

end BstLean.Part203
