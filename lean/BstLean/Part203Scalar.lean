import BstLean.Part196Primitive
import BstLean.Part197Log

/-! Part 203: free root tangents and logarithmic tangents. -/
namespace BstLean.Part203
open MeasureTheory Real

lemma bernoulli_pos {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 < 1 + q * (exp x - 1) := by
  by_cases hq : q = 0
  · simp [hq]
  · have hp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have := mul_pos hp (exp_pos x)
    nlinarith

lemma log_tangent {x x₀ : ℝ} (hx : -1 < x) (hx₀ : -1 < x₀) :
    log (1 + x) ≤ log (1 + x₀) + (x - x₀) / (1 + x₀) := by
  have h0 : 0 < 1 + x₀ := by linarith
  have h1 : 0 < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos h1 h0)
  rw [Real.log_div h1.ne' h0.ne'] at h
  have he : (1 + x) / (1 + x₀) - 1 = (x - x₀) / (1 + x₀) := by
    field_simp
    ring
  rw [he] at h
  linarith

noncomputable def tangentC (x c : ℝ) : ℝ :=
  (log (1 + x) - x / (1 + x)) / c

lemma tangentC_nonneg {x c : ℝ} (hx : -1 < x) (hc : 0 < c) :
    0 ≤ tangentC x c := BstLean.Part197.tangent_constant_nonneg hx hc

lemma log_tangent_div {x x₀ c : ℝ} (hx : -1 < x) (hx₀ : -1 < x₀)
    (hc : 0 < c) :
    log (1 + x) / c ≤ tangentC x₀ c + x / (c * (1 + x₀)) := by
  have h := div_le_div_of_nonneg_right (log_tangent hx hx₀) hc.le
  convert h using 1 <;> unfold tangentC <;> field_simp <;> ring

lemma root_upper {v P H r : ℝ} (hv : 0 ≤ v) (hP : 0 ≤ P)
    (hH : 0 ≤ H) (hr : 0 < r) (he : |√v - √P| ≤ H) :
    v ≤ (1 + H / r) * P + H * r + H ^ 2 := by
  have h := BstLean.Part156.v_le_affine hv hP hH (sq_pos_of_pos hr)
    (by have := (abs_le.mp he).2; linarith)
  simpa [BstLean.Part156.alphaP, BstLean.Part156.betaP, Real.sqrt_sq hr.le,
    add_assoc] using h

lemma root_lower {v P H r : ℝ} (hv : 0 ≤ v) (hP : 0 ≤ P)
    (hH : 0 ≤ H) (hr : H < r) (he : |√v - √P| ≤ H) :
    (1 - H / r) * P - H * r + H ^ 2 ≤ v := by
  have hr0 : 0 < r := lt_of_le_of_lt hH hr
  have hsP := Real.sq_sqrt hP
  have hsv := Real.sq_sqrt hv
  have hab := (abs_le.mp he).1
  have ht : 2 * √P ≤ P / r + r := by
    have heq : P / r + r - 2 * √P = (√P - r) ^ 2 / r := by
      field_simp
      nlinarith [hsP]
    have := div_nonneg (sq_nonneg (√P - r)) hr0.le
    linarith
  have heq : (1 - H / r) * P - H * r + H ^ 2 =
      P - H * (P / r + r) + H ^ 2 := by ring
  rw [heq]
  by_cases hp : H ≤ √P
  · have hs : (√P - H) ^ 2 ≤ v := by
      have := pow_le_pow_left₀ (by linarith : 0 ≤ √P - H)
        (by linarith : √P - H ≤ √v) 2
      rwa [hsv] at this
    have := mul_le_mul_of_nonneg_left ht hH
    nlinarith
  · have hp2 : P ≤ H ^ 2 := by
      nlinarith [Real.sqrt_nonneg P]
    have ha : 0 ≤ 1 - H / r := by
      have := (div_lt_one hr0).mpr hr
      linarith
    have hb := mul_le_mul_of_nonneg_left hp2 ha
    have hneg : (1 - H / r) * H ^ 2 - H * r + H ^ 2 ≤ 0 := by
      have hid : (1 - H / r) * H ^ 2 - H * r + H ^ 2 =
          -H * (r - H) ^ 2 / r := by field_simp; ring
      rw [hid]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)) hr0.le
    nlinarith

end BstLean.Part203
