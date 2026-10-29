import BstLean.Part150Mom

/-!
# Part 150, item 2, tools: Gaussian integrals

* `gauss_cos`, `gauss_sin`: `E cos(tZ) = e^{−t²/2}`, `E sin(tZ) = 0` (`Z` standard Gaussian).
* `gauss_cos_shift`, `gauss_sin_shift`: `E cos(t(x + Z)) = cos(tx)e^{−t²/2}` and the same for `sin`.
* `gauss_abs`: `E|Z| = √(2/π)`.
* `integral_mul_exp_Ioi`: `∫_a^∞ t e^{−t²/2} dt = e^{−a²/2}`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part130 BstLean.Part137 BstLean.Part141

lemma gauss_cos_sin (t : ℝ) :
    ∫ z, Real.cos (t * z) ∂gaussianReal 0 1 = rexp (-(t ^ 2 / 2)) ∧
      ∫ z, Real.sin (t * z) ∂gaussianReal 0 1 = 0 := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) t
  rw [charFun_apply_real] at h
  have e : ∀ x : ℝ, ((t : ℂ) * x * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by
    intro x; push_cast; ring
  have hint : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hre : ∫ x : ℝ, Complex.reCLM (Complex.exp (t * x * Complex.I)) ∂gaussianReal 0 1 =
      Complex.reCLM (∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂gaussianReal 0 1) :=
    ContinuousLinearMap.integral_comp_comm _ hint
  have him : ∫ x : ℝ, Complex.imCLM (Complex.exp (t * x * Complex.I)) ∂gaussianReal 0 1 =
      Complex.imCLM (∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂gaussianReal 0 1) :=
    ContinuousLinearMap.integral_comp_comm _ hint
  rw [h] at hre him
  have e2 : ((t : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - (((1 : NNReal) : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) =
      ((-(t ^ 2 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e2, ← Complex.ofReal_exp] at hre him
  constructor
  · calc ∫ z, Real.cos (t * z) ∂gaussianReal 0 1
        = ∫ x : ℝ, Complex.reCLM (Complex.exp (t * x * Complex.I)) ∂gaussianReal 0 1 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show _ = (Complex.exp (t * x * Complex.I)).re
          rw [e, Complex.exp_ofReal_mul_I_re]
      _ = Complex.reCLM ((rexp (-(t ^ 2 / 2)) : ℝ) : ℂ) := hre
      _ = rexp (-(t ^ 2 / 2)) := Complex.ofReal_re (rexp (-(t ^ 2 / 2)))
  · calc ∫ z, Real.sin (t * z) ∂gaussianReal 0 1
        = ∫ x : ℝ, Complex.imCLM (Complex.exp (t * x * Complex.I)) ∂gaussianReal 0 1 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show _ = (Complex.exp (t * x * Complex.I)).im
          rw [e, Complex.exp_ofReal_mul_I_im]
      _ = Complex.imCLM ((rexp (-(t ^ 2 / 2)) : ℝ) : ℂ) := him
      _ = 0 := Complex.ofReal_im (rexp (-(t ^ 2 / 2)))

lemma integrable_cos_gauss (t c : ℝ) :
    Integrable (fun z : ℝ => Real.cos (t * z + c)) (gaussianReal 0 1) :=
  (integrable_const (1 : ℝ)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun x => by simpa using Real.abs_cos_le_one _)

lemma integrable_sin_gauss (t c : ℝ) :
    Integrable (fun z : ℝ => Real.sin (t * z + c)) (gaussianReal 0 1) :=
  (integrable_const (1 : ℝ)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun x => by simpa using Real.abs_sin_le_one _)

/-- `E cos(t(x + Z)) = cos(tx)·e^{−t²/2}`. -/
theorem gauss_cos_shift (t x : ℝ) :
    ∫ z, Real.cos (t * (x + z)) ∂gaussianReal 0 1 = rexp (-(t ^ 2 / 2)) * Real.cos (t * x) := by
  have e : ∀ z : ℝ, Real.cos (t * (x + z)) =
      Real.cos (t * x) * Real.cos (t * z) - Real.sin (t * x) * Real.sin (t * z) := by
    intro z; rw [mul_add, Real.cos_add]
  have h1 := integrable_cos_gauss t 0
  have h2 := integrable_sin_gauss t 0
  simp only [add_zero] at h1 h2
  simp_rw [e]
  rw [integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
    (gauss_cos_sin t).1, (gauss_cos_sin t).2]
  ring

/-- `E sin(t(x + Z)) = sin(tx)·e^{−t²/2}`. -/
theorem gauss_sin_shift (t x : ℝ) :
    ∫ z, Real.sin (t * (x + z)) ∂gaussianReal 0 1 = rexp (-(t ^ 2 / 2)) * Real.sin (t * x) := by
  have e : ∀ z : ℝ, Real.sin (t * (x + z)) =
      Real.sin (t * x) * Real.cos (t * z) + Real.cos (t * x) * Real.sin (t * z) := by
    intro z; rw [mul_add, Real.sin_add]
  have h1 := integrable_cos_gauss t 0
  have h2 := integrable_sin_gauss t 0
  simp only [add_zero] at h1 h2
  simp_rw [e]
  rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
    (gauss_cos_sin t).1, (gauss_cos_sin t).2]
  ring

/-- `∫_a^∞ t e^{−t²/2} dt = e^{−a²/2}`, with integrability. -/
theorem integral_mul_exp_Ioi (a : ℝ) :
    IntegrableOn (fun t : ℝ => t * rexp (-(t ^ 2 / 2))) (Ioi a) ∧
      ∫ t in Ioi a, t * rexp (-(t ^ 2 / 2)) = rexp (-(a ^ 2 / 2)) := by
  have hint : IntegrableOn (fun t : ℝ => t * rexp (-(t ^ 2 / 2))) (Ioi a) := by
    have h := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn (s := Ioi a)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    show t * rexp (-(1 / 2) * t ^ 2) = _
    congr 2; ring
  refine ⟨hint, ?_⟩
  have hd : ∀ x ∈ Ici a, HasDerivAt (fun t : ℝ => -rexp (-(t ^ 2 / 2))) (x * rexp (-(x ^ 2 / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      convert this using 1; ring
    have := (h1.exp).neg
    convert this using 1; ring
  have ht : Tendsto (fun t : ℝ => -rexp (-(t ^ 2 / 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).neg
    simpa using this
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint ht]
  ring

/-- `E|Z| = √(2/π)`. -/
theorem gauss_abs : ∫ z, |z| ∂gaussianReal 0 1 = √(2 / π) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • |x| =
      (fun y : ℝ => (√(2 * π))⁻¹ * (y * rexp (-(y ^ 2 / 2)))) |x| := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero, sq_abs]
    rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) by ring]; ring
  simp_rw [e]
  refine Eq.trans (integral_comp_abs (f := fun y : ℝ => (√(2 * π))⁻¹ * (y * rexp (-(y ^ 2 / 2))))) ?_
  rw [integral_const_mul, (integral_mul_exp_Ioi 0).2]
  have hp : (0 : ℝ) < π := Real.pi_pos
  have h2 : √(2 * π) * √(2 / π) = 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 * π * (2 / π) = 2 ^ 2 by field_simp]
    exact Real.sqrt_sq (by norm_num)
  have h3 : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
    Real.exp_zero, mul_one]
  field_simp
  linarith

end BstLean.Part150
