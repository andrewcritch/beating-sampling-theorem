import BstLean.Part161Defs

/-!
# Part 161, item 1(b): the Gaussian formulas in `ℝⁿ`

Role: `delegations/statements/p161-spec.md`, item 1(b) (and the two-copy integral of item 1(c)).
Do not use `sorry`, `native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:gaussian` (Gaussian
displacement) and Lemma `t7:p07:chi-identity` (the two-copy identity, one pair of components).

* `integral_quad1`: `∫ exp(−(q − 1) z²/2 + β z) dγ(z) = q^{−1/2}·exp(β²/(2q))` for `q > 0`.
* `stdGauss_affine`: the distribution of `μ + √v·η` has the density `gdN μ v` with respect to
  the standard Gaussian distribution; `gauss_event_density`.
* `aff_gdN`: the Hellinger affinity `E √(gdN μ v)`.
* `gauss_root`: `(√P(B) − √Q(B))² ≤ hellG2 n |m₁ − m₂|² S₁ S₂` for `P = N(m₁, S₁ I)`,
  `Q = N(m₂, S₂ I)` and every measurable set `B`, every value of the scales.
* `hellG2_le`, `hellG2_le_window`: the bound of Lemma `t7:p07:gaussian` and the form of the
  specification.
* `twocopy_gdN`: `∫ gdN μ₁ v₁ · gdN μ₂ v₂ dγ`, the integral in the two-copy identity.
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)

/-! ## One coordinate -/

lemma gd1_pos {v : ℝ} (hv : 0 < v) (μ z : ℝ) : 0 < gd1 μ v z := by
  unfold gd1
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hv)) (exp_pos _)

lemma gd1_nonneg (μ v z : ℝ) : 0 ≤ gd1 μ v z := by
  unfold gd1
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (exp_pos _).le

lemma measurable_gd1_joint : Measurable (fun p : ℝ × ℝ × ℝ => gd1 p.1 p.2.1 p.2.2) := by
  unfold gd1
  have m1 : Measurable (fun p : ℝ × ℝ × ℝ => p.1) := measurable_fst
  have m2 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have m3 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  exact (m2.sqrt.inv).mul
    (((((m3.sub m1).pow_const 2).neg.div (measurable_const.mul m2)).add
      ((m3.pow_const 2).div_const 2)).exp)

lemma measurable_gd1 (μ v : ℝ) : Measurable (gd1 μ v) :=
  measurable_gd1_joint.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- **The Gaussian integral of the exponential of a quadratic function.** For `q > 0`:
`∫ exp(−(q − 1) z²/2 + β z) dγ(z) = q^{−1/2}·exp(β²/(2q))`, `γ = N(0, 1)`. -/
theorem integral_quad1 {q : ℝ} (hq : 0 < q) (β : ℝ) :
    Integrable (fun z : ℝ => exp (-(q - 1) * z ^ 2 / 2 + β * z)) (gaussianReal 0 1) ∧
    ∫ z, exp (-(q - 1) * z ^ 2 / 2 + β * z) ∂gaussianReal 0 1 =
      (√q)⁻¹ * exp (β ^ 2 / (2 * q)) := by
  have hb : 0 < q / 2 := by positivity
  have he : (fun z : ℝ => gaussianPDFReal 0 1 z • exp (-(q - 1) * z ^ 2 / 2 + β * z)) =
      fun z => ((√(2 * π))⁻¹ * exp (β ^ 2 / (2 * q))) * exp (-(q / 2) * (z - β / q) ^ 2) := by
    funext z
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,
      mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  have hi : Integrable (fun z : ℝ => exp (-(q / 2) * (z - β / q) ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).comp_sub_right (β / q)
  constructor
  · rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    have e2 : (fun z : ℝ => (gaussianPDF 0 1 z).toReal • exp (-(q - 1) * z ^ 2 / 2 + β * z)) =
        fun z => gaussianPDFReal 0 1 z • exp (-(q - 1) * z ^ 2 / 2 + β * z) := by
      funext z
      rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    rw [e2, he]
    exact hi.const_mul _
  · rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    rw [he, integral_const_mul,
      integral_sub_right_eq_self (fun z : ℝ => exp (-(q / 2) * z ^ 2)) (β / q),
      integral_gaussian]
    have hp := Real.pi_pos
    have hdiv : π / (q / 2) = (2 * π) / q := by field_simp
    rw [hdiv, Real.sqrt_div (by positivity), div_eq_mul_inv]
    have h2 : √(2 * π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp

/-- The same with a constant factor and a constant in the exponent. -/
lemma integral_quadK {q : ℝ} (hq : 0 < q) (β κ C : ℝ) :
    Integrable (fun z : ℝ => C * exp (-(q - 1) * z ^ 2 / 2 + β * z + κ)) (gaussianReal 0 1) ∧
    ∫ z, C * exp (-(q - 1) * z ^ 2 / 2 + β * z + κ) ∂gaussianReal 0 1 =
      C * exp κ * ((√q)⁻¹ * exp (β ^ 2 / (2 * q))) := by
  obtain ⟨h1, h2⟩ := integral_quad1 hq β
  have e : (fun z : ℝ => C * exp (-(q - 1) * z ^ 2 / 2 + β * z + κ)) =
      fun z => (C * exp κ) * exp (-(q - 1) * z ^ 2 / 2 + β * z) := by
    funext z
    rw [Real.exp_add]
    ring
  rw [e]
  exact ⟨h1.const_mul _, by rw [integral_const_mul, h2]⟩

/-- The variance `v > 0` as a nonnegative real number. -/
noncomputable def vNN (v : ℝ) : ℝ≥0 := ⟨max v 0, le_max_right _ _⟩

lemma coe_vNN {v : ℝ} (hv : 0 < v) : ((vNN v : ℝ≥0) : ℝ) = v := max_eq_left hv.le

/-- The distribution of `μ + √v·η`, `η` standard Gaussian, is `N(μ, v)`. -/
lemma gauss1_affine (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    (gaussianReal 0 1).map (fun y => μ + √v * y) = gaussianReal μ (vNN v) := by
  have e : (fun y : ℝ => μ + √v * y) = (fun y => μ + y) ∘ (fun y => √v * y) := rfl
  rw [e, ← Measure.map_map (measurable_const_add μ) (measurable_const_mul _),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  congr 1
  · simp
  · apply NNReal.eq
    simp [coe_vNN hv, Real.sq_sqrt hv.le]

/-- `N(μ, v) = gd1 μ v · N(0, 1)`. -/
lemma gauss1_dens (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    gaussianReal μ (vNN v) =
      (gaussianReal 0 1).withDensity (fun y => ENNReal.ofReal (gd1 μ v y)) := by
  have hv' : vNN v ≠ 0 := by
    intro h
    have h' := congrArg NNReal.toReal h
    rw [coe_vNN hv, NNReal.coe_zero] at h'
    exact hv.ne' h'
  rw [gaussianReal_of_var_ne_zero _ hv', gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) (measurable_gd1 μ v).ennreal_ofReal]
  congr 1
  funext y
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, gd1, coe_vNN hv, NNReal.coe_one, sub_zero, mul_one]
  have h1 : √(2 * π * v) = √(2 * π) * √v := Real.sqrt_mul (by positivity) _
  rw [h1, mul_mul_mul_comm, ← Real.exp_add, mul_inv]
  congr 2
  ring

lemma gd1_eq (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    gd1 μ v = fun z => (√v)⁻¹ * exp (-(1 / v - 1) * z ^ 2 / 2 + μ / v * z + -μ ^ 2 / (2 * v)) := by
  funext z
  unfold gd1
  congr 2
  field_simp
  ring

lemma integrable_gd1 (μ : ℝ) {v : ℝ} (hv : 0 < v) : Integrable (gd1 μ v) (gaussianReal 0 1) := by
  rw [gd1_eq μ hv]
  exact (integral_quadK (by positivity) _ _ _).1

lemma integral_gd1 (μ : ℝ) {v : ℝ} (hv : 0 < v) : ∫ y, gd1 μ v y ∂gaussianReal 0 1 = 1 := by
  have h : ∫⁻ y, ENNReal.ofReal (gd1 μ v y) ∂gaussianReal 0 1 = 1 := by
    have h' : ∫⁻ y, ENNReal.ofReal (gd1 μ v y) ∂gaussianReal 0 1 =
        ((gaussianReal 0 1).withDensity (fun y => ENNReal.ofReal (gd1 μ v y))) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h', ← gauss1_dens μ hv, measure_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gd1 μ hv)
    (Filter.Eventually.of_forall fun y => gd1_nonneg μ v y), ← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun y => gd1_nonneg μ v y)
    zero_le_one).mp h

/-- The square root of `gd1`. -/
noncomputable def rt1 (μ v z : ℝ) : ℝ := (√(√v))⁻¹ * exp (-(z - μ) ^ 2 / (4 * v) + z ^ 2 / 4)

lemma rt1_nonneg (μ v z : ℝ) : 0 ≤ rt1 μ v z :=
  mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (exp_pos _).le

lemma rt1_sq (μ v z : ℝ) : rt1 μ v z ^ 2 = gd1 μ v z := by
  unfold rt1 gd1
  rw [mul_pow, inv_pow, Real.sq_sqrt (Real.sqrt_nonneg _), ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

lemma sqrt_gd1 (μ v z : ℝ) : √(gd1 μ v z) = rt1 μ v z := by
  rw [← rt1_sq, Real.sqrt_sq (rt1_nonneg μ v z)]

/-- The affinity in one coordinate. -/
lemma integral_rt1 (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    Integrable (rt1 μ v) (gaussianReal 0 1) ∧
    ∫ z, rt1 μ v z ∂gaussianReal 0 1 =
      √(2 * √v / (1 + v)) * exp (-(μ ^ 2) / (4 * (1 + v))) := by
  have hq : 0 < (1 + v) / (2 * v) := by positivity
  have e : rt1 μ v = fun z => (√(√v))⁻¹ *
      exp (-((1 + v) / (2 * v) - 1) * z ^ 2 / 2 + μ / (2 * v) * z + -μ ^ 2 / (4 * v)) := by
    funext z
    unfold rt1
    congr 2
    field_simp
    ring
  obtain ⟨h1, h2⟩ := integral_quadK hq (μ / (2 * v)) (-μ ^ 2 / (4 * v)) (√(√v))⁻¹
  rw [e]
  refine ⟨h1, ?_⟩
  rw [h2]
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv
  have c1 : (√(√v))⁻¹ * (√((1 + v) / (2 * v)))⁻¹ = √(2 * √v / (1 + v)) := by
    rw [← mul_inv, ← Real.sqrt_mul hsv.le, ← Real.sqrt_inv]
    congr 1
    have hvv : v = √v * √v := (Real.mul_self_sqrt hv.le).symm
    field_simp
    nlinarith [hvv]
  have c2 : exp (-μ ^ 2 / (4 * v)) * exp ((μ / (2 * v)) ^ 2 / (2 * ((1 + v) / (2 * v)))) =
      exp (-(μ ^ 2) / (4 * (1 + v))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc (√(√v))⁻¹ * exp (-μ ^ 2 / (4 * v)) *
        ((√((1 + v) / (2 * v)))⁻¹ * exp ((μ / (2 * v)) ^ 2 / (2 * ((1 + v) / (2 * v)))))
      = ((√(√v))⁻¹ * (√((1 + v) / (2 * v)))⁻¹) *
        (exp (-μ ^ 2 / (4 * v)) * exp ((μ / (2 * v)) ^ 2 / (2 * ((1 + v) / (2 * v))))) := by ring
    _ = _ := by rw [c1, c2]

/-- The two-copy integral in one coordinate. -/
lemma twocopy_gd1 (μ₁ μ₂ : ℝ) {v₁ v₂ : ℝ} (h1 : 0 < v₁) (h2 : 0 < v₂)
    (hD : 0 < v₁ + v₂ - v₁ * v₂) :
    Integrable (fun z => gd1 μ₁ v₁ z * gd1 μ₂ v₂ z) (gaussianReal 0 1) ∧
    ∫ z, gd1 μ₁ v₁ z * gd1 μ₂ v₂ z ∂gaussianReal 0 1 =
      (√(v₁ + v₂ - v₁ * v₂))⁻¹ *
        exp ((2 * (μ₁ * μ₂) + μ₁ ^ 2 * (v₂ - 1) + μ₂ ^ 2 * (v₁ - 1)) /
          (2 * (v₁ + v₂ - v₁ * v₂))) := by
  set D := v₁ + v₂ - v₁ * v₂ with hDdef
  have hq : 0 < D / (v₁ * v₂) := by positivity
  have e : (fun z => gd1 μ₁ v₁ z * gd1 μ₂ v₂ z) = fun z => ((√v₁)⁻¹ * (√v₂)⁻¹) *
      exp (-(D / (v₁ * v₂) - 1) * z ^ 2 / 2 + (μ₁ / v₁ + μ₂ / v₂) * z +
        (-μ₁ ^ 2 / (2 * v₁) + -μ₂ ^ 2 / (2 * v₂))) := by
    funext z
    unfold gd1
    rw [mul_mul_mul_comm, ← Real.exp_add]
    congr 2
    rw [hDdef]
    field_simp
    ring
  obtain ⟨i1, i2⟩ := integral_quadK hq (μ₁ / v₁ + μ₂ / v₂)
    (-μ₁ ^ 2 / (2 * v₁) + -μ₂ ^ 2 / (2 * v₂)) ((√v₁)⁻¹ * (√v₂)⁻¹)
  rw [e]
  refine ⟨i1, ?_⟩
  rw [i2]
  have c1 : (√v₁)⁻¹ * (√v₂)⁻¹ * (√(D / (v₁ * v₂)))⁻¹ = (√D)⁻¹ := by
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul h1.le, ← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  have c2 : exp (-μ₁ ^ 2 / (2 * v₁) + -μ₂ ^ 2 / (2 * v₂)) *
      exp ((μ₁ / v₁ + μ₂ / v₂) ^ 2 / (2 * (D / (v₁ * v₂)))) =
      exp ((2 * (μ₁ * μ₂) + μ₁ ^ 2 * (v₂ - 1) + μ₂ ^ 2 * (v₁ - 1)) / (2 * D)) := by
    rw [← Real.exp_add]
    congr 1
    have hD' : D ≠ 0 := hD.ne'
    rw [hDdef] at hD' ⊢
    field_simp
    ring
  calc (√v₁)⁻¹ * (√v₂)⁻¹ * exp (-μ₁ ^ 2 / (2 * v₁) + -μ₂ ^ 2 / (2 * v₂)) *
        ((√(D / (v₁ * v₂)))⁻¹ * exp ((μ₁ / v₁ + μ₂ / v₂) ^ 2 / (2 * (D / (v₁ * v₂)))))
      = ((√v₁)⁻¹ * (√v₂)⁻¹ * (√(D / (v₁ * v₂)))⁻¹) *
        (exp (-μ₁ ^ 2 / (2 * v₁) + -μ₂ ^ 2 / (2 * v₂)) *
          exp ((μ₁ / v₁ + μ₂ / v₂) ^ 2 / (2 * (D / (v₁ * v₂))))) := by ring
    _ = _ := by rw [c1, c2]

/-! ## The vector -/

variable {ι : Type*} [Fintype ι]

lemma gdN_pos {v : ℝ} (hv : 0 < v) (μ z : ι → ℝ) : 0 < gdN μ v z :=
  Finset.prod_pos fun i _ => gd1_pos hv (μ i) (z i)

lemma gdN_nonneg (μ : ι → ℝ) (v : ℝ) (z : ι → ℝ) : 0 ≤ gdN μ v z :=
  Finset.prod_nonneg fun i _ => gd1_nonneg (μ i) v (z i)

/-- The density `gdN` is measurable in the mean, the variance and the point together. -/
lemma measurable_gdN_joint :
    Measurable (fun p : ((ι → ℝ) × ℝ) × (ι → ℝ) => gdN p.1.1 p.1.2 p.2) := by
  unfold gdN
  refine Finset.measurable_prod _ fun i _ => ?_
  have hm : Measurable (fun p : ((ι → ℝ) × ℝ) × (ι → ℝ) => ((p.1.1 i, p.1.2, p.2 i) : ℝ × ℝ × ℝ)) :=
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact measurable_gd1_joint.comp hm

lemma measurable_gdN (μ : ι → ℝ) (v : ℝ) : Measurable (gdN μ v) :=
  measurable_gdN_joint.comp ((measurable_const.prodMk measurable_const).prodMk measurable_id)

/-- **The distribution of `μ + √v·η` has the density `gdN μ v` with respect to the standard
Gaussian distribution.** -/
theorem stdGauss_affine (μ : ι → ℝ) {v : ℝ} (hv : 0 < v) :
    (stdGauss ι).map (fun η => μ + √v • η) =
      (stdGauss ι).withDensity (fun z => ENNReal.ofReal (gdN μ v z)) := by
  classical
  have e1 : (stdGauss ι).map (fun η => μ + √v • η) =
      Measure.pi (fun i : ι => gaussianReal (μ i) (vNN v)) := by
    unfold stdGauss
    have h := Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
      (f := fun i : ι => fun y : ℝ => μ i + √v * y)
      (hμ := fun i => by rw [gauss1_affine (μ i) hv]; infer_instance)
      (fun _ => ((measurable_const_mul _).const_add _).aemeasurable)
    have h2 : (fun η : ι → ℝ => μ + √v • η) = fun x i => μ i + √v * x i := by
      funext x i; simp
    rw [h2, h]
    congr 1
    funext i
    exact gauss1_affine (μ i) hv
  rw [e1]
  refine Measure.pi_eq fun S hS => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS),
    ← lintegral_indicator (MeasurableSet.univ_pi hS)]
  have hind : ∀ x : ι → ℝ, (Set.pi Set.univ S).indicator
      (fun x => ENNReal.ofReal (gdN μ v x)) x =
      ENNReal.ofReal (∏ i, (S i).indicator (gd1 (μ i) v) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ S
    · rw [Set.indicator_of_mem hx]
      congr 1
      unfold gdN
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ S i := by
        by_contra hcon
        push Not at hcon
        exact hx fun i _ => hcon i
      obtain ⟨i, hi⟩ := this
      have : ∏ i, (S i).indicator (gd1 (μ i) v) (x i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      rw [this, ENNReal.ofReal_zero]
  simp_rw [hind]
  have hint : ∀ i, Integrable ((S i).indicator (gd1 (μ i) v)) (gaussianReal 0 1) := fun i =>
    (integrable_gd1 (μ i) hv).indicator (hS i)
  have hnn : ∀ i y, 0 ≤ (S i).indicator (gd1 (μ i) v) y := fun i y =>
    Set.indicator_nonneg (fun y _ => gd1_nonneg (μ i) v y) y
  have hI : Integrable (fun x : ι → ℝ => ∏ i, (S i).indicator (gd1 (μ i) v) (x i))
      (stdGauss ι) := by
    unfold stdGauss
    exact Integrable.fintype_prod_dep hint
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hnn i (x i))]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i => (S i).indicator (gd1 (μ i) v)),
    ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg (hnn i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gauss1_dens (μ i) hv, withDensity_apply _ (hS i), integral_indicator (hS i),
    ofReal_integral_eq_lintegral_ofReal (integrable_gd1 (μ i) hv).integrableOn
      (Filter.Eventually.of_forall fun y => gd1_nonneg (μ i) v y)]

lemma integrable_gdN (μ : ι → ℝ) {v : ℝ} (hv : 0 < v) : Integrable (gdN μ v) (stdGauss ι) := by
  unfold stdGauss gdN
  exact Integrable.fintype_prod_dep fun i => integrable_gd1 (μ i) hv

lemma integral_gdN (μ : ι → ℝ) {v : ℝ} (hv : 0 < v) : ∫ z, gdN μ v z ∂stdGauss ι = 1 := by
  unfold stdGauss gdN
  rw [integral_fintype_prod_eq_prod (fun i : ι => gd1 (μ i) v)]
  simp [integral_gd1 _ hv]

/-- `E g(μ + √v·η) = E[g(z)·gdN μ v z]`. -/
theorem integral_affine (μ : ι → ℝ) {v : ℝ} (hv : 0 < v) {g : (ι → ℝ) → ℝ} (hg : Measurable g) :
    ∫ η, g (μ + √v • η) ∂stdGauss ι = ∫ z, g z * gdN μ v z ∂stdGauss ι := by
  rw [← BstLean.Part138.integral_dens (stdGauss ι) (measurable_gdN μ v) (gdN_nonneg μ v),
    ← stdGauss_affine μ hv,
    integral_map ((measurable_const_smul (√v)).const_add μ).aemeasurable hg.aestronglyMeasurable]

/-- **The probability of an event under `N(μ, v·I)` as an integral of the density.** -/
theorem gauss_event_density (μ : ι → ℝ) {v : ℝ} (hv : 0 < v) {B : Set (ι → ℝ)}
    (hB : MeasurableSet B) :
    (stdGauss ι).real {η | μ + √v • η ∈ B} = ∫ z, B.indicator 1 z * gdN μ v z ∂stdGauss ι := by
  have hm : Measurable (fun η : ι → ℝ => μ + √v • η) := (measurable_const_smul (√v)).const_add μ
  have h : (stdGauss ι).real {η | μ + √v • η ∈ B} =
      ∫ η, ((fun η : ι → ℝ => μ + √v • η) ⁻¹' B).indicator 1 η ∂stdGauss ι :=
    (integral_indicator_one (hm hB)).symm
  rw [h, ← integral_affine μ hv (measurable_one.indicator hB)]
  rfl

/-- **The Hellinger affinity** of `N(μ, v·I)` and the standard Gaussian distribution:
`E √(gdN μ v) = (2√v/(1 + v))^{n/2}·exp(−|μ|²/(4(1 + v)))`. -/
theorem aff_gdN (μ : ι → ℝ) {v : ℝ} (hv : 0 < v) :
    ∫ z, √(gdN μ v z) ∂stdGauss ι =
      √(2 * √v / (1 + v)) ^ Fintype.card ι * exp (-(normSq μ) / (4 * (1 + v))) := by
  have e : (fun z : ι → ℝ => √(gdN μ v z)) = fun z => ∏ i, rt1 (μ i) v (z i) := by
    funext z
    have h : gdN μ v z = (∏ i, rt1 (μ i) v (z i)) ^ 2 := by
      unfold gdN
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => (rt1_sq _ _ _).symm
    rw [h, Real.sqrt_sq (Finset.prod_nonneg fun i _ => rt1_nonneg _ _ _)]
  rw [e]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i : ι => rt1 (μ i) v)]
  simp_rw [(integral_rt1 _ hv).2]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  unfold normSq
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- **The two-copy integral** (Lemma `t7:p07:chi-identity` for one pair of components): for
`D = v₁ + v₂ − v₁v₂ > 0`,
`∫ gdN μ₁ v₁ · gdN μ₂ v₂ dγ = D^{−n/2}·exp((2⟨μ₁, μ₂⟩ + |μ₁|²(v₂ − 1) + |μ₂|²(v₁ − 1))/(2D))`. -/
theorem twocopy_gdN (μ₁ μ₂ : ι → ℝ) {v₁ v₂ : ℝ} (h1 : 0 < v₁) (h2 : 0 < v₂)
    (hD : 0 < v₁ + v₂ - v₁ * v₂) :
    Integrable (fun z => gdN μ₁ v₁ z * gdN μ₂ v₂ z) (stdGauss ι) ∧
    ∫ z, gdN μ₁ v₁ z * gdN μ₂ v₂ z ∂stdGauss ι =
      (√(v₁ + v₂ - v₁ * v₂))⁻¹ ^ Fintype.card ι *
        exp ((2 * ∑ i, μ₁ i * μ₂ i + normSq μ₁ * (v₂ - 1) + normSq μ₂ * (v₁ - 1)) /
          (2 * (v₁ + v₂ - v₁ * v₂))) := by
  have e : (fun z : ι → ℝ => gdN μ₁ v₁ z * gdN μ₂ v₂ z) =
      fun z => ∏ i, (fun y => gd1 (μ₁ i) v₁ y * gd1 (μ₂ i) v₂ y) (z i) := by
    funext z
    unfold gdN
    rw [← Finset.prod_mul_distrib]
  rw [e]
  unfold stdGauss
  refine ⟨Integrable.fintype_prod_dep fun i => (twocopy_gd1 (μ₁ i) (μ₂ i) h1 h2 hD).1, ?_⟩
  rw [integral_fintype_prod_eq_prod (fun (i : ι) (y : ℝ) => gd1 (μ₁ i) v₁ y * gd1 (μ₂ i) v₂ y)]
  simp_rw [(twocopy_gd1 _ _ h1 h2 hD).2]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  unfold normSq
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]

/-! ## The squared Hellinger distance `hellG2` -/

lemma hellG2_ratio_le_one {S₁ S₂ : ℝ} (h1 : 0 < S₁) (h2 : 0 < S₂) :
    2 * √(S₁ * S₂) / (S₁ + S₂) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have e : √(S₁ * S₂) = √S₁ * √S₂ := Real.sqrt_mul h1.le _
  rw [e]
  nlinarith [sq_nonneg (√S₁ - √S₂), Real.sq_sqrt h1.le, Real.sq_sqrt h2.le]

lemma hellG2_le_two (n : ℕ) (d2 S₁ S₂ : ℝ) : hellG2 n d2 S₁ S₂ ≤ 2 := by
  unfold hellG2
  split_ifs
  · have : 0 ≤ √(2 * √(S₁ * S₂) / (S₁ + S₂)) ^ n * exp (-d2 / (4 * (S₁ + S₂))) :=
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (exp_pos _).le
    linarith
  · exact le_rfl

lemma hellG2_nonneg (n : ℕ) {d2 : ℝ} (hd : 0 ≤ d2) (S₁ S₂ : ℝ) : 0 ≤ hellG2 n d2 S₁ S₂ := by
  unfold hellG2
  split_ifs with h
  · have ha : √(2 * √(S₁ * S₂) / (S₁ + S₂)) ≤ 1 :=
      (Real.sqrt_le_sqrt (hellG2_ratio_le_one h.1 h.2)).trans_eq Real.sqrt_one
    have hp : √(2 * √(S₁ * S₂) / (S₁ + S₂)) ^ n ≤ 1 := pow_le_one₀ (Real.sqrt_nonneg _) ha
    have hs : 0 < S₁ + S₂ := add_pos h.1 h.2
    have he : exp (-d2 / (4 * (S₁ + S₂))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have := mul_le_mul hp he (exp_pos _).le zero_le_one
    linarith
  · norm_num

lemma measurable_hellG2 (n : ℕ) :
    Measurable (fun p : ℝ × ℝ × ℝ => hellG2 n p.1 p.2.1 p.2.2) := by
  unfold hellG2
  have m1 : Measurable (fun p : ℝ × ℝ × ℝ => p.1) := measurable_fst
  have m2 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have m3 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const m2).inter (measurableSet_lt measurable_const m3)
  · exact measurable_const.sub (measurable_const.mul
      (((((measurable_const.mul (m2.mul m3).sqrt).div (m2.add m3)).sqrt).pow_const n).mul
        ((m1.neg.div (measurable_const.mul (m2.add m3))).exp)))

/-- **The root comparison of two Gaussian distributions with scalar covariance.** For every
measurable set `B` and every value of the scales:
`(√N(m₁, S₁ I)(B) − √N(m₂, S₂ I)(B))² ≤ hellG2 n |m₁ − m₂|² S₁ S₂`. -/
theorem gauss_root {n : ℕ} (m₁ m₂ : Fin n → ℝ) (S₁ S₂ : ℝ) {B : Set (Fin n → ℝ)}
    (hB : MeasurableSet B) :
    (√((stdGauss (Fin n)).real {η | m₁ + √S₁ • η ∈ B}) -
      √((stdGauss (Fin n)).real {η | m₂ + √S₂ • η ∈ B})) ^ 2 ≤
      hellG2 n (normSq (m₁ - m₂)) S₁ S₂ := by
  by_cases h : 0 < S₁ ∧ 0 < S₂
  · obtain ⟨h1, h2⟩ := h
    have hs2 : 0 < √S₂ := Real.sqrt_pos.mpr h2
    set μ : Fin n → ℝ := (√S₂)⁻¹ • (m₁ - m₂) with hμ
    set v : ℝ := S₁ / S₂ with hv
    have hv0 : 0 < v := div_pos h1 h2
    set B' : Set (Fin n → ℝ) := {z | m₂ + √S₂ • z ∈ B} with hB'
    have mB' : MeasurableSet B' :=
      ((measurable_const_smul (√S₂)).const_add m₂) hB
    have e1 : {η : Fin n → ℝ | m₁ + √S₁ • η ∈ B} = {η | μ + √v • η ∈ B'} := by
      ext η
      change m₁ + √S₁ • η ∈ B ↔ m₂ + √S₂ • (μ + √v • η) ∈ B
      have : m₂ + √S₂ • (μ + √v • η) = m₁ + √S₁ • η := by
        rw [smul_add, hμ, smul_smul, smul_smul, mul_inv_cancel₀ hs2.ne', one_smul, hv,
          ← Real.sqrt_mul h2.le, mul_div_cancel₀ _ h2.ne']
        abel
      rw [this]
    have e2 : (stdGauss (Fin n)).real {η | m₂ + √S₂ • η ∈ B} = (stdGauss (Fin n)).real B' := rfl
    rw [e1, e2, gauss_event_density μ hv0 mB']
    have hsq : ∀ z, √(gdN μ v z) ^ 2 = gdN μ v z := fun z => Real.sq_sqrt (gdN_nonneg μ v z)
    have hr := BstLean.Part157.root_set_hell (stdGauss (Fin n)) (a := fun z => √(gdN μ v z))
      (measurable_gdN μ v).sqrt (fun z => Real.sqrt_nonneg _)
      (by simp_rw [hsq]; exact integrable_gdN μ hv0)
      (by simp_rw [hsq]; exact integral_gdN μ hv0) mB'
    simp_rw [hsq] at hr
    rw [aff_gdN μ hv0, Fintype.card_fin] at hr
    refine hr.trans (le_of_eq ?_)
    unfold hellG2
    split_ifs with hh
    swap
    · exact absurd ⟨h1, h2⟩ hh
    have c1 : 2 * √v / (1 + v) = 2 * √(S₁ * S₂) / (S₁ + S₂) := by
      have : √v = √(S₁ * S₂) / S₂ := by
        rw [hv, Real.sqrt_mul h1.le, Real.sqrt_div h1.le]
        have := Real.mul_self_sqrt h2.le
        field_simp
        nlinarith
      rw [this, hv]
      field_simp
      ring
    have c2 : -(normSq μ) / (4 * (1 + v)) = -(normSq (m₁ - m₂)) / (4 * (S₁ + S₂)) := by
      have : normSq μ = normSq (m₁ - m₂) / S₂ := by
        unfold normSq
        rw [hμ, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt h2.le]
        field_simp
      rw [this, hv]
      field_simp
      ring
    rw [c1, c2]
  · unfold hellG2
    split_ifs
    have b1 : ∀ S : Set (Fin n → ℝ), √((stdGauss (Fin n)).real S) ≤ 1 := fun S => by
      have := Real.sqrt_le_sqrt (measureReal_le_one (μ := stdGauss (Fin n)) (s := S))
      rwa [Real.sqrt_one] at this
    have h1 := b1 {η | m₁ + √S₁ • η ∈ B}
    have h2 := b1 {η | m₂ + √S₂ • η ∈ B}
    have h3 := Real.sqrt_nonneg ((stdGauss (Fin n)).real {η | m₁ + √S₁ • η ∈ B})
    have h4 := Real.sqrt_nonneg ((stdGauss (Fin n)).real {η | m₂ + √S₂ • η ∈ B})
    nlinarith

/-- **The Gaussian displacement bound** (Lemma `t7:p07:gaussian`): with `R = S₁/S₂`,
`H² ≤ n(R − 1)²/(8R) + d2/(2(S₁ + S₂))`. -/
theorem hellG2_le (n : ℕ) {d2 S₁ S₂ : ℝ} (h1 : 0 < S₁) (h2 : 0 < S₂) (_hd : 0 ≤ d2) :
    hellG2 n d2 S₁ S₂ ≤
      n * (S₁ / S₂ - 1) ^ 2 / (8 * (S₁ / S₂)) + d2 / (2 * (S₁ + S₂)) := by
  unfold hellG2
  split_ifs with hh
  swap
  · exact absurd ⟨h1, h2⟩ hh
  set y : ℝ := (S₁ / S₂ - 1) ^ 2 / (4 * (S₁ / S₂)) with hy
  set A : ℝ := √(2 * √(S₁ * S₂) / (S₁ + S₂)) with hA
  have hs : 0 < S₁ + S₂ := add_pos h1 h2
  have hR : 0 < S₁ / S₂ := div_pos h1 h2
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA4 : A ^ 4 = 1 / (1 + y) := by
    have e1 : A ^ 2 = 2 * √(S₁ * S₂) / (S₁ + S₂) := Real.sq_sqrt (by positivity)
    have e2 : A ^ 4 = (A ^ 2) ^ 2 := by ring
    rw [e2, e1, div_pow, mul_pow, Real.sq_sqrt (by positivity), hy]
    field_simp
    ring
  have hexp : exp (-y) ≤ A ^ 4 := by
    rw [hA4, Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp y])
  have hA1 : exp (-y / 4) ≤ A := by
    have e : exp (-y) = exp (-y / 4) ^ 4 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e] at hexp
    exact le_of_pow_le_pow_left₀ (by norm_num) hA0 hexp
  have hAn : exp (-(n * y / 4)) ≤ A ^ n := by
    have e : exp (-(n * y / 4)) = exp (-y / 4) ^ n := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [e]
    exact pow_le_pow_left₀ (exp_pos _).le hA1 n
  have hx : exp (-(n * y / 4) + -d2 / (4 * (S₁ + S₂))) ≤
      A ^ n * exp (-d2 / (4 * (S₁ + S₂))) := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right hAn (exp_pos _).le
  have hlin := Real.add_one_le_exp (-(n * y / 4) + -d2 / (4 * (S₁ + S₂)))
  have e3 : (n : ℝ) * (S₁ / S₂ - 1) ^ 2 / (8 * (S₁ / S₂)) = n * y / 2 := by
    rw [hy]; field_simp; ring
  have e4 : d2 / (2 * (S₁ + S₂)) = -2 * (-d2 / (4 * (S₁ + S₂))) := by
    field_simp; ring
  rw [e3, e4]
  linarith

/-- **The Gaussian displacement bound in the form of the specification**: if
`|S₁/S₂ − 1| ≤ ε < 1`, then `H² ≤ n(S₁/S₂ − 1)²/(4(1 − ε)²) + d2/(2 S₂)`. -/
theorem hellG2_le_window (n : ℕ) {d2 S₁ S₂ ε : ℝ} (h1 : 0 < S₁) (h2 : 0 < S₂) (hd : 0 ≤ d2)
    (hε : |S₁ / S₂ - 1| ≤ ε) (hε1 : ε < 1) :
    hellG2 n d2 S₁ S₂ ≤ n * (S₁ / S₂ - 1) ^ 2 / (4 * (1 - ε) ^ 2) + d2 / (2 * S₂) := by
  refine (hellG2_le n h1 h2 hd).trans ?_
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hε
  have hR : 1 - ε ≤ S₁ / S₂ := by linarith [(abs_le.mp hε).1]
  have hpos : 0 < 1 - ε := by linarith
  have a1 : (n : ℝ) * (S₁ / S₂ - 1) ^ 2 / (8 * (S₁ / S₂)) ≤
      n * (S₁ / S₂ - 1) ^ 2 / (4 * (1 - ε) ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have a2 : d2 / (2 * (S₁ + S₂)) ≤ d2 / (2 * S₂) :=
    div_le_div_of_nonneg_left hd (by positivity) (by linarith)
  linarith

end BstLean.Part161

open BstLean.Part161 in
#print axioms integral_quad1
open BstLean.Part161 in
#print axioms stdGauss_affine
open BstLean.Part161 in
#print axioms gauss_event_density
open BstLean.Part161 in
#print axioms aff_gdN
open BstLean.Part161 in
#print axioms twocopy_gdN
open BstLean.Part161 in
#print axioms gauss_root
open BstLean.Part161 in
#print axioms hellG2_le
open BstLean.Part161 in
#print axioms hellG2_le_window
