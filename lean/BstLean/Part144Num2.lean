import BstLean.Part144Num

/-!
# Part 144, the four-term Mills lower bound and numeric bounds at level `2`

Role: `delegations/statements/p144-spec.md` (numerics for item 2, `sampleFails144`).
`φ = gaussianPDFReal 0 1`, `Φ̄(t) = (gaussianReal 0 1).real (Ioi t)`.

* `mills4_lower`: `Φ̄(t) ≥ φ(t)·(t³ + 5t)/(t⁴ + 6t² + 3)` for `t > 0`.
* `tail4_of_mills`: its numeric form at `t = √z`.
* `exp_two_bounds`: `7.38905609 ≤ exp 2 ≤ 7.38905611`.
* `tail4_2`: `Φ̄(2) > 0.02259`.
* `kappa_bounds_of`: two-sided bounds of `κ = φ(√z)/(2√z)`.
* `kappa2_lower`, `kappa2_upper`: `0.013497 ≤ φ(2)/4 ≤ 0.013498`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open BstLean.Part131

/-- **The four-term Mills lower bound**: `Φ̄(t) ≥ φ(t)·(t³ + 5t)/(t⁴ + 6t² + 3)` for `t > 0`. -/
theorem mills4_lower {t : ℝ} (_ht : 0 < t) :
    gaussianPDFReal 0 1 t * ((t ^ 3 + 5 * t) / (t ^ 4 + 6 * t ^ 2 + 3)) ≤
      (gaussianReal 0 1).real (Ioi t) := by
  have hint := integrable_gaussianPDFReal 0 1
  rw [gauss_real_eq]
  let f : ℝ → ℝ := fun x =>
    -(gaussianPDFReal 0 1 x * ((x ^ 3 + 5 * x) / (x ^ 4 + 6 * x ^ 2 + 3)))
  let f' : ℝ → ℝ := fun x =>
    gaussianPDFReal 0 1 x * (1 - 24 / (x ^ 4 + 6 * x ^ 2 + 3) ^ 2)
  have hq : ∀ x : ℝ, 0 < x ^ 4 + 6 * x ^ 2 + 3 := fun x => by positivity
  have hderiv : ∀ x ∈ Ici t, HasDerivAt f (f' x) x := by
    intro x _
    have hp : HasDerivAt (fun x : ℝ => x ^ 3 + 5 * x) (3 * x ^ 2 + 5) x := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
        simpa using hasDerivAt_pow 3 x
      have h2 : HasDerivAt (fun x : ℝ => 5 * x) 5 x := by
        simpa using (hasDerivAt_id x).const_mul 5
      exact h1.add h2
    have hqd : HasDerivAt (fun x : ℝ => x ^ 4 + 6 * x ^ 2 + 3) (4 * x ^ 3 + 12 * x) x := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * x ^ 3) x := by
        simpa using hasDerivAt_pow 4 x
      have h2 : HasDerivAt (fun x : ℝ => 6 * x ^ 2) (12 * x) x := by
        have h := (hasDerivAt_pow 2 x).const_mul 6
        convert h using 1
        simp; ring
      exact (h1.add h2).add_const 3
    have h3 := ((pdf_hasDerivAt x).mul (hp.div hqd (hq x).ne')).neg
    have e4 : f' x = -(gaussianPDFReal 0 1 x * -x * ((x ^ 3 + 5 * x) / (x ^ 4 + 6 * x ^ 2 + 3)) +
        gaussianPDFReal 0 1 x * (((3 * x ^ 2 + 5) * (x ^ 4 + 6 * x ^ 2 + 3) -
          (x ^ 3 + 5 * x) * (4 * x ^ 3 + 12 * x)) / (x ^ 4 + 6 * x ^ 2 + 3) ^ 2)) := by
      have := (hq x).ne'
      simp only [f']
      field_simp
      ring
    rw [e4]; exact h3
  have hbd0 : ∀ x : ℝ, 0 ≤ 24 / (x ^ 4 + 6 * x ^ 2 + 3) ^ 2 := fun x => by positivity
  have hbd2 : ∀ x : ℝ, 24 / (x ^ 4 + 6 * x ^ 2 + 3) ^ 2 ≤ 3 := by
    intro x
    rw [div_le_iff₀ (by positivity)]
    have h4 : 0 ≤ x ^ 4 := by positivity
    have h2 : 0 ≤ x ^ 2 := by positivity
    have : (3 : ℝ) ≤ x ^ 4 + 6 * x ^ 2 + 3 := by linarith
    nlinarith
  have hmeas : Measurable fun x : ℝ => 1 - 24 / (x ^ 4 + 6 * x ^ 2 + 3) ^ 2 := by
    fun_prop
  have hf'int : IntegrableOn f' (Ioi t) := by
    refine Integrable.mono' (hint.const_mul 2).integrableOn
      ((hint.aestronglyMeasurable.mul hmeas.aestronglyMeasurable).restrict) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    have hp := gaussianPDFReal_nonneg 0 1 x
    simp only [f', Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg hp, mul_comm]
    have h1 := hbd0 x
    have h2 := hbd2 x
    have : |1 - 24 / (x ^ 4 + 6 * x ^ 2 + 3) ^ 2| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    exact mul_le_mul_of_nonneg_right this hp
  have htend : Tendsto f atTop (𝓝 0) := by
    have hb : ∀ᶠ x : ℝ in atTop, ‖f x‖ ≤ phi1 * Real.exp (1 / 2) * x⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hr0 : 0 ≤ (x ^ 3 + 5 * x) / (x ^ 4 + 6 * x ^ 2 + 3) := by positivity
      have hr : (x ^ 3 + 5 * x) / (x ^ 4 + 6 * x ^ 2 + 3) ≤ x⁻¹ := by
        rw [div_le_iff₀ (hq x), inv_mul_eq_div, le_div_iff₀ hx]
        nlinarith [sq_nonneg x]
      simp only [f, norm_neg, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) hr0), pdf_eq_phi1]
      have : Real.exp ((1 - x ^ 2) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
      have h2 := phi1_pos
      gcongr
    have h0 : Tendsto (fun x : ℝ => phi1 * Real.exp (1 / 2) * x⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (phi1 * Real.exp (1 / 2))
    exact squeeze_zero_norm' hb h0
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hf'int htend
  have hle : ∫ x in Ioi t, f' x ≤ ∫ x in Ioi t, gaussianPDFReal 0 1 x := by
    refine setIntegral_mono_on hf'int hint.integrableOn measurableSet_Ioi ?_
    intro x _
    have hp := gaussianPDFReal_nonneg 0 1 x
    have h1 := hbd0 x
    simp only [f']
    nlinarith
  rw [hI] at hle
  have hft : f t = -(gaussianPDFReal 0 1 t * ((t ^ 3 + 5 * t) / (t ^ 4 + 6 * t ^ 2 + 3))) := rfl
  rw [hft, zero_sub, neg_neg] at hle
  exact hle

/-- A numeric form of the four-term Mills bound at `t = √z`: from `tl ≤ √z` (as `tl² ≤ z`) and
`exp(z/2) ≤ E`. -/
theorem tail4_of_mills {z tl E : ℝ} (hz : 0 < z) (htl0 : 0 ≤ tl) (htl : tl ^ 2 ≤ z)
    (hE0 : 0 < E) (hE : Real.exp (z / 2) ≤ E) :
    (100000 / 250664 : ℝ) * (1 / E) * (tl * (z + 5) / (z ^ 2 + 6 * z + 3)) ≤
      (gaussianReal 0 1).real (Ioi (Real.sqrt z)) := by
  set t : ℝ := Real.sqrt z with ht
  have htsq : t ^ 2 = z := Real.sq_sqrt hz.le
  have ht1 : tl ≤ t := by rw [ht]; exact Real.le_sqrt_of_sq_le htl
  have htpos : 0 < t := Real.sqrt_pos.mpr hz
  have hm := mills4_lower htpos
  have e : (t ^ 3 + 5 * t) / (t ^ 4 + 6 * t ^ 2 + 3) = t * (z + 5) / (z ^ 2 + 6 * z + 3) := by
    rw [← htsq]; ring
  rw [e, pdf_eq, htsq] at hm
  have hsq : (0 : ℝ) < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h1 : √(2 * Real.pi) ≤ 250664 / 100000 := by
    have := sqrt_two_pi_bounds.2
    norm_num at this ⊢; linarith
  have hc : (100000 / 250664 : ℝ) ≤ (√(2 * Real.pi))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hsq]
    refine h1.trans (le_of_eq ?_)
    norm_num
  have hEn : 1 / E ≤ Real.exp (-(z / 2)) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos _) hE
  have hprod : (100000 / 250664 : ℝ) * (1 / E) ≤ (√(2 * Real.pi))⁻¹ * Real.exp (-(z / 2)) :=
    mul_le_mul hc hEn (by positivity) (by positivity)
  have hfrac : tl * (z + 5) / (z ^ 2 + 6 * z + 3) ≤ t * (z + 5) / (z ^ 2 + 6 * z + 3) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht1 (by positivity)) (by positivity)
  have hall := mul_le_mul hprod hfrac (by positivity) (by positivity)
  exact hall.trans hm

lemma exp_two_bounds :
    (738905609 : ℝ) / 100000000 ≤ Real.exp 2 ∧ Real.exp 2 ≤ 738905611 / 100000000 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have hp := Real.exp_pos 1
  have e : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  constructor <;> nlinarith

lemma sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- **`Φ̄(2) > 0.02259`.** -/
theorem tail4_2 : (2259 : ℝ) / 100000 < (gaussianReal 0 1).real (Ioi 2) := by
  have hE : Real.exp ((4 : ℝ) / 2) ≤ 738905611 / 100000000 := by
    rw [show ((4 : ℝ) / 2) = 2 by norm_num]; exact exp_two_bounds.2
  have h := tail4_of_mills (z := 4) (tl := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hE
  rw [sqrt_four] at h
  refine lt_of_lt_of_le ?_ h
  norm_num

/-- **Two-sided bounds of `κ = φ(√z)/(2√z)`** from bounds of `√z` and `exp(z/2)`. -/
theorem kappa_bounds_of {z tl tu El Eu : ℝ} (hz : 0 < z) (htl0 : 0 < tl) (htl : tl ^ 2 ≤ z)
    (htu0 : 0 < tu) (htu : z ≤ tu ^ 2) (hEl0 : 0 < El) (hEl : El ≤ Real.exp (z / 2))
    (hEu : Real.exp (z / 2) ≤ Eu) :
    1 / (2506629 / 1000000 * Eu * (2 * tu)) ≤
        gaussianPDFReal 0 1 (Real.sqrt z) / (2 * Real.sqrt z) ∧
      gaussianPDFReal 0 1 (Real.sqrt z) / (2 * Real.sqrt z) ≤
        1 / (2506627 / 1000000 * El * (2 * tl)) := by
  obtain ⟨hS1, hS2⟩ := sqrt_two_pi_bounds
  set t : ℝ := Real.sqrt z with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr hz
  have ht1 : tl ≤ t := by rw [ht]; exact Real.le_sqrt_of_sq_le htl
  have ht2 : t ≤ tu := by
    rw [ht, Real.sqrt_le_left htu0.le]; exact htu
  have hs : (0 : ℝ) < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hE0 : 0 < Real.exp (z / 2) := Real.exp_pos _
  have hEu0 : 0 < Eu := lt_of_lt_of_le hE0 hEu
  have e : gaussianPDFReal 0 1 t / (2 * t) = 1 / (√(2 * Real.pi) * Real.exp (z / 2) * (2 * t)) := by
    rw [pdf_eq, Real.sq_sqrt hz.le, Real.exp_neg]
    field_simp
  rw [e]
  constructor
  · refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul (mul_le_mul hS2 hEu hE0.le (by norm_num)) (by linarith) (by positivity)
      (by positivity)
  · refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul (mul_le_mul hS1 hEl hEl0.le hs.le) (by linarith) (by positivity)
      (by positivity)

/-- `0.013497 ≤ φ(2)/4`. -/
theorem kappa2_lower : (13497 : ℝ) / 1000000 ≤ gaussianPDFReal 0 1 2 / (2 * 2) := by
  obtain ⟨h1, h2⟩ := exp_two_bounds
  have h := (kappa_bounds_of (z := 4) (tl := 2) (tu := 2) (El := 738905609 / 100000000)
    (Eu := 738905611 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [show ((4 : ℝ) / 2) = 2 by norm_num]; exact h1)
    (by rw [show ((4 : ℝ) / 2) = 2 by norm_num]; exact h2)).1
  rw [sqrt_four] at h
  refine le_trans ?_ h
  norm_num

/-- `φ(2)/4 ≤ 0.013498`. -/
theorem kappa2_upper : gaussianPDFReal 0 1 2 / (2 * 2) ≤ (13498 : ℝ) / 1000000 := by
  obtain ⟨h1, h2⟩ := exp_two_bounds
  have h := (kappa_bounds_of (z := 4) (tl := 2) (tu := 2) (El := 738905609 / 100000000)
    (Eu := 738905611 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [show ((4 : ℝ) / 2) = 2 by norm_num]; exact h1)
    (by rw [show ((4 : ℝ) / 2) = 2 by norm_num]; exact h2)).2
  rw [sqrt_four] at h
  refine h.trans ?_
  norm_num

end BstLean.Part144

open BstLean.Part144 in
#print axioms mills4_lower
open BstLean.Part144 in
#print axioms tail4_of_mills
open BstLean.Part144 in
#print axioms tail4_2
open BstLean.Part144 in
#print axioms kappa_bounds_of
open BstLean.Part144 in
#print axioms kappa2_lower
open BstLean.Part144 in
#print axioms kappa2_upper
