import BstLean.Part130Sym

/-!
# Part 131, the one-dimensional Gaussian tail

Role: `delegations/statements/p131-spec.md`, item 1 (the facts about `Φ̄` that the block lemma
needs). `γ = gaussianReal 0 1` is the standard Gaussian on `ℝ`; `Φ̄(t) = γ(t, ∞)` is written
`(gaussianReal 0 1).real (Set.Ioi t)`; `φ(1) = phi1`.

* `tail_line`: for `t ≥ 0`: `Φ̄(t) ≥ Φ̄(1) + (φ(1)/2)(1 − t²)`. This is the supporting line at
  `z = 1` of the convex function `z ↦ Φ̄(√z)` of the paper (round onW4c, "Confirmed probability
  argument"); the supporting line is all that the Jensen step needs.
* `mills_one`: `Φ̄(1) ≥ φ(1)/2` (the Mills bound at `1`).
* `phi1_gt`: `φ(1) > 6/25`. So `Φ̄(1) > 3/25` (`tail_one_gt`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- `φ(1)`, the standard Gaussian density at `1`. -/
noncomputable def phi1 : ℝ := gaussianPDFReal 0 1 1

lemma pdf_eq (x : ℝ) : gaussianPDFReal 0 1 x = (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp [gaussianPDFReal, neg_div]

lemma phi1_pos : 0 < phi1 := by
  unfold phi1; rw [pdf_eq]; positivity

lemma pdf_eq_phi1 (x : ℝ) : gaussianPDFReal 0 1 x = phi1 * Real.exp ((1 - x ^ 2) / 2) := by
  unfold phi1
  rw [pdf_eq, pdf_eq, mul_assoc, ← Real.exp_add]
  congr 2; ring

lemma pdf_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : phi1 * x ≤ gaussianPDFReal 0 1 x := by
  rw [pdf_eq_phi1]
  have h : (1 : ℝ) ≤ Real.exp ((1 - x ^ 2) / 2) := Real.one_le_exp (by nlinarith)
  have := phi1_pos
  nlinarith

lemma pdf_le {x : ℝ} (h1 : 1 ≤ x) : gaussianPDFReal 0 1 x ≤ phi1 * x := by
  rw [pdf_eq_phi1]
  have h : Real.exp ((1 - x ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have := phi1_pos
  nlinarith

lemma gauss_real_eq (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ x in s, gaussianPDFReal 0 1 x := by
  rw [Measure.real, gaussianReal_apply_eq_integral 0 one_ne_zero s,
    ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _)]

lemma integral_Ioc_lin {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioc a b, phi1 * x = phi1 / 2 * (b ^ 2 - a ^ 2) := by
  rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul, integral_id]
  ring

lemma intOn_lin (a b : ℝ) : IntegrableOn (fun x : ℝ => phi1 * x) (Ioc a b) :=
  (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- **The supporting line of `z ↦ Φ̄(√z)` at `z = 1`**, in the variable `t = √z`. -/
theorem tail_line {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1).real (Ioi 1) + phi1 / 2 * (1 - t ^ 2) ≤ (gaussianReal 0 1).real (Ioi t) := by
  have hint := integrable_gaussianPDFReal 0 1
  rcases le_total t 1 with h | h
  · have hu : Ioi t = Ioc t 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi h).symm
    have hd : Disjoint (Ioc t 1) (Ioi 1) := by
      rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.mpr hx')
    rw [hu, measureReal_union hd measurableSet_Ioi, gauss_real_eq (Ioc t 1)]
    have h1 : ∫ x in Ioc t 1, phi1 * x ≤ ∫ x in Ioc t 1, gaussianPDFReal 0 1 x := by
      refine setIntegral_mono_on (intOn_lin t 1) hint.integrableOn measurableSet_Ioc ?_
      intro x hx; exact pdf_ge (ht.trans hx.1.le) hx.2
    rw [integral_Ioc_lin h] at h1
    linarith
  · have hu : Ioi 1 = Ioc 1 t ∪ Ioi t := (Ioc_union_Ioi_eq_Ioi h).symm
    have hd : Disjoint (Ioc 1 t) (Ioi t) := by
      rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.mpr hx')
    rw [hu, measureReal_union hd measurableSet_Ioi, gauss_real_eq (Ioc 1 t)]
    have h1 : ∫ x in Ioc 1 t, gaussianPDFReal 0 1 x ≤ ∫ x in Ioc 1 t, phi1 * x := by
      refine setIntegral_mono_on hint.integrableOn (intOn_lin 1 t) measurableSet_Ioc ?_
      intro x hx; exact pdf_le hx.1.le
    rw [integral_Ioc_lin h] at h1
    linarith

/-- **The Mills bound at `1`**: `Φ̄(1) ≥ φ(1)/2`. -/
theorem mills_one : phi1 / 2 ≤ (gaussianReal 0 1).real (Ioi 1) := by
  have hint := integrable_gaussianPDFReal 0 1
  rw [gauss_real_eq]
  -- `f = −φ(x)/x`, `f′ = φ(x)(1 + 1/x²) ≤ 2φ(x)` on `x ≥ 1`
  let f : ℝ → ℝ := fun x => -(gaussianPDFReal 0 1 x / x)
  let f' : ℝ → ℝ := fun x => gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2)
  have hderiv : ∀ x ∈ Ici (1 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le one_pos hx).ne'
    have h1 : HasDerivAt (fun x : ℝ => gaussianPDFReal 0 1 x)
        (gaussianPDFReal 0 1 x * (-x)) x := by
      have h2 : HasDerivAt (fun x : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)))
          ((√(2 * Real.pi))⁻¹ * (Real.exp (-(x ^ 2 / 2)) * (-(2 * x ^ 1 * 1 / 2)))) x :=
        (((hasDerivAt_id x).pow 2).div_const 2).neg.exp.const_mul _
      have e : (fun x : ℝ => gaussianPDFReal 0 1 x) =
          fun x : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := funext pdf_eq
      rw [e, pdf_eq]
      convert h2 using 1; ring
    have h3 := (h1.div (hasDerivAt_id x) hx0).neg
    have h4 : HasDerivAt f
        (-((gaussianPDFReal 0 1 x * -x * id x - gaussianPDFReal 0 1 x * 1) / id x ^ 2)) x := h3
    have e4 : f' x =
        -((gaussianPDFReal 0 1 x * -x * id x - gaussianPDFReal 0 1 x * 1) / id x ^ 2) := by
      simp only [f', id]
      field_simp
      ring
    rw [e4]; exact h4
  have hf'int : IntegrableOn f' (Ioi 1) := by
    refine Integrable.mono' (hint.const_mul 2).integrableOn
      ((hint.aestronglyMeasurable.mul (measurable_const.add (measurable_const.div (measurable_id.pow_const 2))).aestronglyMeasurable).restrict) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : (1 : ℝ) < x := hx
    have hp := gaussianPDFReal_nonneg 0 1 x
    have h2 : 1 / x ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h3 : 0 ≤ 1 / x ^ 2 := by positivity
    simp only [f', Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have htend : Tendsto f atTop (𝓝 0) := by
    have hb : ∀ᶠ x : ℝ in atTop, ‖f x‖ ≤ phi1 * Real.exp (1 / 2) * x⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp only [f, norm_neg, Real.norm_eq_abs]
      rw [abs_of_nonneg (div_nonneg (gaussianPDFReal_nonneg _ _ _) hx.le), pdf_eq_phi1,
        div_eq_mul_inv]
      have : Real.exp ((1 - x ^ 2) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
      have h2 := phi1_pos
      have h3 : 0 < x⁻¹ := inv_pos.mpr hx
      gcongr
    have h0 : Tendsto (fun x : ℝ => phi1 * Real.exp (1 / 2) * x⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (phi1 * Real.exp (1 / 2))
    exact squeeze_zero_norm' hb h0
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hf'int htend
  have hle : ∫ x in Ioi (1 : ℝ), f' x ≤ ∫ x in Ioi (1 : ℝ), 2 * gaussianPDFReal 0 1 x := by
    refine setIntegral_mono_on hf'int (hint.const_mul 2).integrableOn measurableSet_Ioi ?_
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hp := gaussianPDFReal_nonneg 0 1 x
    have h2 : 1 / x ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    simp only [f']
    nlinarith
  rw [integral_const_mul, hI] at hle
  have hf1 : f 1 = -phi1 := by simp [f, phi1]
  rw [hf1] at hle
  linarith

/-- `φ(1) > 6/25`. -/
theorem phi1_gt : 6 / 25 < phi1 := by
  unfold phi1
  rw [pdf_eq]
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : 0 < Real.pi := Real.pi_pos
  -- `exp(−1/2) = 1/√e`
  have h1 : Real.exp (-((1 : ℝ) ^ 2 / 2)) = (√(Real.exp 1))⁻¹ := by
    rw [← Real.exp_half, ← Real.exp_neg]; norm_num
  rw [h1, ← mul_inv, ← Real.sqrt_mul (by positivity)]
  have h2 : √(2 * Real.pi * Real.exp 1) < 25 / 6 := by
    rw [Real.sqrt_lt' (by norm_num)]
    have : Real.pi * Real.exp 1 < 3.15 * 2.7182818286 := by
      apply mul_lt_mul hpi he.le (Real.exp_pos 1) (by norm_num)
    nlinarith
  have h3 : 0 < √(2 * Real.pi * Real.exp 1) := Real.sqrt_pos.mpr (by positivity)
  rw [lt_inv_comm₀ (by norm_num) h3]
  convert h2 using 1; norm_num

/-- `Φ̄(1) > 3/25`. -/
theorem tail_one_gt : 3 / 25 < (gaussianReal 0 1).real (Ioi 1) := by
  have := mills_one; have := phi1_gt; linarith

/-- The symmetry of the standard Gaussian: `γ(−∞, −t) = γ(t, ∞)`. -/
theorem tail_neg (t : ℝ) : (gaussianReal 0 1).real (Iio (-t)) = (gaussianReal 0 1).real (Ioi t) := by
  have h := gaussianReal_map_neg (μ := 0) (v := 1)
  rw [neg_zero] at h
  have e : (fun x : ℝ => -x) ⁻¹' Ioi t = Iio (-t) := by
    ext x; simp only [mem_preimage, mem_Ioi, mem_Iio]; constructor <;> intro h <;> linarith
  conv_rhs => rw [← h]
  rw [map_measureReal_apply measurable_neg measurableSet_Ioi, e]

end BstLean.Part131

open BstLean.Part131 in
#print axioms tail_line
open BstLean.Part131 in
#print axioms mills_one
open BstLean.Part131 in
#print axioms tail_one_gt
