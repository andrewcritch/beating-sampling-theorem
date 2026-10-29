import BstLean.Part229Cap
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Derivatives on the two open branches and on the cap level set. -/
namespace BstLean.Part229
open Real Filter Topology
open BstLean.Part188

noncomputable def capSlope (a d f : ℝ) : ℝ :=
  if d < a - f ^ 2 then f / ((a - f ^ 2) * √(a - f ^ 2)) else 0

lemma capSlope_measurable (a d : ℝ) : Measurable (capSlope a d) := by
  unfold capSlope
  exact Measurable.ite (isOpen_lt continuous_const (by fun_prop)).measurableSet
    (by fun_prop) measurable_const

lemma capSlope_bound {a d f R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (hf : |f| ≤ R) :
    |capSlope a d f| ≤ R / (d * √d) := by
  unfold capSlope
  split_ifs with h
  · have hY : 0 < a - f ^ 2 := hd.trans h
    have hden : d * √d ≤ (a - f ^ 2) * √(a - f ^ 2) :=
      mul_le_mul h.le (Real.sqrt_le_sqrt h.le) (Real.sqrt_nonneg _) hY.le
    rw [abs_div, abs_of_pos (mul_pos hY (Real.sqrt_pos.mpr hY))]
    exact (div_le_div_of_nonneg_right hf (by positivity)).trans
      (div_le_div_of_nonneg_left hR (by positivity) hden)
  · simp only [abs_zero]
    positivity

theorem weight_hasDerivAt_active {a d f : ℝ} (hd : 0 < d) (hf : d < a - f ^ 2) :
    HasDerivAt (weight a d) (f / ((a - f ^ 2) * √(a - f ^ 2))) f := by
  have hY : 0 < a - f ^ 2 := hd.trans hf
  have hbase : HasDerivAt (fun x : ℝ => a - x ^ 2) (-(2 * f)) f := by
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * f) f := by
      convert (hasDerivAt_id f).pow 2 using 1 <;> first | rfl | simp
    convert (hasDerivAt_const f a).sub hsq using 1 <;> first | rfl | simp only [zero_sub]
  have hs := hbase.sqrt hY.ne'
  have hi := hs.inv (Real.sqrt_pos.mpr hY).ne'
  have he : weight a d =ᶠ[𝓝 f] fun x : ℝ => (√(a - x ^ 2))⁻¹ := by
    have hc : Continuous (fun x : ℝ => a - x ^ 2) := by fun_prop
    filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hf)] with x hx
    rw [weight_eq_inv_sqrt, max_eq_left hx.le]
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert hi using 1
  have hs0 : √(a - f ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hY).ne'
  field_simp
  rw [Real.sq_sqrt hY.le]

theorem weight_hasDerivAt_capped {a d f : ℝ} (hf : a - f ^ 2 < d) :
    HasDerivAt (weight a d) 0 f := by
  have he : weight a d =ᶠ[𝓝 f] fun _ : ℝ => (√d)⁻¹ := by
    have hc : Continuous (fun x : ℝ => a - x ^ 2) := by fun_prop
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hf)] with x hx
    rw [weight_eq_inv_sqrt, max_eq_right hx.le]
  exact (hasDerivAt_const f ((√d)⁻¹)).congr_of_eventuallyEq he

theorem weight_hasDerivAt_off_boundary {a d f : ℝ} (hd : 0 < d)
    (hf : a - f ^ 2 ≠ d) : HasDerivAt (weight a d) (capSlope a d f) f := by
  rcases lt_or_gt_of_ne hf with h | h
  · simpa [capSlope, not_lt.mpr h.le] using weight_hasDerivAt_capped h
  · simpa [capSlope, h] using weight_hasDerivAt_active hd h

theorem weight_comp_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a d : ℝ} (hd : 0 < d) (f : E → ℝ) {x : E} (hx : a - f x ^ 2 = d) :
    fderiv ℝ (fun y => weight a d (f y)) x = 0 := by
  have he : weight a d (f x) = (√d)⁻¹ := by
    rw [weight_eq_inv_sqrt, hx, max_self]
  have hm : IsLocalMax (fun y => weight a d (f y)) x := by
    apply Filter.Eventually.of_forall
    intro y
    change weight a d (f y) ≤ weight a d (f x)
    rw [he]
    exact weight_le hd
  exact hm.fderiv_eq_zero

theorem weight_comp_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a d : ℝ} (hd : 0 < d) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => weight a d (f y)) x = capSlope a d (f x) • fderiv ℝ f x := by
  by_cases hb : a - f x ^ 2 = d
  · rw [weight_comp_boundary hd f hb]
    simp [capSlope, hb]
  · exact (weight_hasDerivAt_off_boundary hd hb).comp_hasFDerivAt x hf.hasFDerivAt |>.fderiv

theorem capped_test_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a d : ℝ} (hd : 0 < d) {f z : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hz : DifferentiableAt ℝ z x)
    (hp : DifferentiableAt ℝ (fun y => weight a d (f y)) x) :
    fderiv ℝ (fun y => weight a d (f y) * z y) x =
      weight a d (f x) • fderiv ℝ z x +
        (z x * capSlope a d (f x)) • fderiv ℝ f x := by
  rw [fderiv_fun_mul hp hz, weight_comp_fderiv hd hf, smul_smul]

end BstLean.Part229
