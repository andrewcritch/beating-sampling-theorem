import BstLean.Part138Hell

/-!
# Part 138, item 2: the Hellinger distance of two isotropic Gaussian vectors with one centre

Role: `delegations/statements/p138-spec.md`. Paper sources: `onW5-opus-prover.md` §4.5
(Lemma D3), `onW5c-cx.md` §5, `onW6c-cx.md` §6.

`γ` is a standard Gaussian vector of `ℝ^ι` (`stdGauss ι`), `s > 0`.

* `dens1 s`: the density of `N(0, s²)` with respect to `N(0, 1)` on `ℝ`; `gauss1_density`.
* `densN s`: the density of `s·γ` with respect to `γ` (a product); `stdGauss_scale`.
* `integral_scale`: `E g(s·γ) = E[densN s(γ)·g(γ)]`.
* `aff_densN`: the affinity `E √(densN s(γ)) = (√(2s/(1 + s²)))^n`, `n` the dimension.
* `hellG n τ τ₀ = 2 − 2·(√(2ττ₀/(τ² + τ₀²)))^n`: the squared Hellinger distance of
  `N(c, τ²I_n)` and `N(c, τ₀²I_n)` (the paper's `2 − 2(2√r/(1 + r))^{n/2}`, `r = τ²/τ₀²`).
* `hellG_le`: for `n ≥ 2`: `hellG n τ τ₀ ≤ n(τ − τ₀)²/(τ² + τ₀²)`
  (the paper's `n(r − 1)²/((1 + √r)²(1 + r))`); `hellG_le_two`, `hellG_nonneg`.
* **`gaussScale138`**: for bounded measurable `f`:
  `(E f(c + τγ) − E f(c + τ₀γ))² ≤ 2·hellG n τ τ₀·(E f(c + τγ)² + E f(c + τ₀γ)²)`.
  `f` is arbitrary, so the bound passes to every image, in particular under `sphPt`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part138

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part133 (sq_integral_le)

/-! ## One coordinate -/

/-- The density of `N(0, s²)` with respect to `N(0, 1)`. -/
noncomputable def dens1 (s y : ℝ) : ℝ := s⁻¹ * rexp (-(y ^ 2) * (s⁻¹ ^ 2 - 1) / 2)

/-- The square root of `dens1`. -/
noncomputable def root1 (s y : ℝ) : ℝ := √(s⁻¹) * rexp (-(y ^ 2) * (s⁻¹ ^ 2 - 1) / 4)

lemma dens1_pos {s : ℝ} (hs : 0 < s) (y : ℝ) : 0 < dens1 s y := by
  unfold dens1; positivity

lemma root1_nonneg (s y : ℝ) : 0 ≤ root1 s y := by
  unfold root1; positivity

lemma root1_sq {s : ℝ} (hs : 0 < s) (y : ℝ) : root1 s y ^ 2 = dens1 s y := by
  unfold root1 dens1
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hs.le), ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

lemma measurable_dens1 (s : ℝ) : Measurable (dens1 s) := by
  unfold dens1
  exact ((((measurable_id.pow_const 2).neg.mul_const _).div_const _).exp).const_mul _

lemma measurable_root1 (s : ℝ) : Measurable (root1 s) := by
  unfold root1
  exact ((((measurable_id.pow_const 2).neg.mul_const _).div_const _).exp).const_mul _

/-- The variance `s²` as a nonnegative real number. -/
noncomputable def vS (s : ℝ) : ℝ≥0 := ⟨s ^ 2, sq_nonneg s⟩

lemma coe_vS (s : ℝ) : ((vS s : ℝ≥0) : ℝ) = s ^ 2 := rfl

/-- `N(0, s²) = dens1 s · N(0, 1)`. -/
lemma gauss1_density {s : ℝ} (hs : 0 < s) :
    gaussianReal 0 (vS s) =
      (gaussianReal 0 1).withDensity (fun y => ENNReal.ofReal (dens1 s y)) := by
  have hv : vS s ≠ 0 := by
    intro h
    have h' := congrArg NNReal.toReal h
    rw [coe_vS, NNReal.coe_zero] at h'
    exact (pow_pos hs 2).ne' h'
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) (measurable_dens1 s).ennreal_ofReal]
  congr 1
  funext y
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, dens1, coe_vS, NNReal.coe_one, sub_zero, mul_one]
  have h1 : √(2 * π * s ^ 2) = √(2 * π) * s := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]
  rw [h1, mul_mul_mul_comm, ← Real.exp_add, mul_inv]
  congr 2
  field_simp
  ring

lemma integrable_dens1 {s : ℝ} (hs : 0 < s) : Integrable (dens1 s) (gaussianReal 0 1) := by
  refine ⟨(measurable_dens1 s).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y => (dens1_pos hs y).le)]
  have h : ∫⁻ y, ENNReal.ofReal (dens1 s y) ∂gaussianReal 0 1 =
      ((gaussianReal 0 1).withDensity (fun y => ENNReal.ofReal (dens1 s y))) Set.univ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [h, ← gauss1_density hs, measure_univ]
  exact ENNReal.one_lt_top

lemma integral_dens1 {s : ℝ} (hs : 0 < s) : ∫ y, dens1 s y ∂gaussianReal 0 1 = 1 := by
  have h : ∫⁻ y, ENNReal.ofReal (dens1 s y) ∂gaussianReal 0 1 = 1 := by
    have h' : ∫⁻ y, ENNReal.ofReal (dens1 s y) ∂gaussianReal 0 1 =
        ((gaussianReal 0 1).withDensity (fun y => ENNReal.ofReal (dens1 s y))) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h', ← gauss1_density hs, measure_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_dens1 hs)
    (Filter.Eventually.of_forall fun y => (dens1_pos hs y).le), ← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun y => (dens1_pos hs y).le)
    zero_le_one).mp h

/-- The affinity in one coordinate: `E √(dens1 s) = √(2s/(1 + s²))`. -/
lemma integral_root1 {s : ℝ} (hs : 0 < s) :
    ∫ y, root1 s y ∂gaussianReal 0 1 = √(2 * s / (1 + s ^ 2)) := by
  set s' : ℝ := √(2 * s ^ 2 / (1 + s ^ 2)) with hs'
  have hpos : 0 < 2 * s ^ 2 / (1 + s ^ 2) := by positivity
  have hs'0 : 0 < s' := Real.sqrt_pos.mpr hpos
  have hs'2 : s' ^ 2 = 2 * s ^ 2 / (1 + s ^ 2) := Real.sq_sqrt hpos.le
  have e : ∀ y, root1 s y = √(s⁻¹) * s' * dens1 s' y := by
    intro y
    unfold root1 dens1
    have h1 : s'⁻¹ ^ 2 - 1 = (s⁻¹ ^ 2 - 1) / 2 := by
      rw [inv_pow, hs'2]
      field_simp
      ring
    rw [h1]
    have h2 : -(y ^ 2) * ((s⁻¹ ^ 2 - 1) / 2) / 2 = -(y ^ 2) * (s⁻¹ ^ 2 - 1) / 4 := by ring
    rw [h2]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, integral_dens1 hs'0, mul_one, hs',
    ← Real.sqrt_mul (inv_nonneg.mpr hs.le)]
  congr 1
  field_simp

/-! ## The vector -/

variable {ι : Type*} [Fintype ι]

/-- The density of `s·γ` with respect to `γ`. -/
noncomputable def densN (s : ℝ) (x : ι → ℝ) : ℝ := ∏ i, dens1 s (x i)

/-- The square root of `densN`. -/
noncomputable def rootN (s : ℝ) (x : ι → ℝ) : ℝ := ∏ i, root1 s (x i)

lemma densN_nonneg {s : ℝ} (hs : 0 < s) (x : ι → ℝ) : 0 ≤ densN s x :=
  Finset.prod_nonneg fun i _ => (dens1_pos hs (x i)).le

lemma rootN_nonneg (s : ℝ) (x : ι → ℝ) : 0 ≤ rootN s x :=
  Finset.prod_nonneg fun i _ => root1_nonneg s (x i)

lemma rootN_sq {s : ℝ} (hs : 0 < s) (x : ι → ℝ) : rootN s x ^ 2 = densN s x := by
  unfold rootN densN
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => root1_sq hs (x i)

lemma measurable_densN (s : ℝ) : Measurable (densN (ι := ι) s) := by
  unfold densN
  exact Finset.measurable_prod _ fun i _ => (measurable_dens1 s).comp (measurable_pi_apply i)

lemma measurable_rootN (s : ℝ) : Measurable (rootN (ι := ι) s) := by
  unfold rootN
  exact Finset.measurable_prod _ fun i _ => (measurable_root1 s).comp (measurable_pi_apply i)

/-- **The distribution of `s·γ` has the density `densN s` with respect to `γ`.** -/
theorem stdGauss_scale {s : ℝ} (hs : 0 < s) :
    (stdGauss ι).map (fun x => s • x) =
      (stdGauss ι).withDensity (fun x => ENNReal.ofReal (densN s x)) := by
  classical
  have e1 : (stdGauss ι).map (fun x => s • x) =
      Measure.pi (fun _ : ι => gaussianReal 0 (vS s)) := by
    unfold stdGauss
    have h := Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
      (f := fun _ : ι => fun y : ℝ => s * y)
      (hμ := fun _ => by rw [gaussianReal_map_const_mul]; infer_instance)
      (fun _ => (measurable_const_mul s).aemeasurable)
    have h2 : (fun x : ι → ℝ => s • x) = fun x i => s * x i := by
      funext x i; simp
    rw [h2, h]
    congr 1
    funext i
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    rfl
  rw [e1]
  refine Measure.pi_eq fun S hS => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS),
    ← lintegral_indicator (MeasurableSet.univ_pi hS)]
  have hind : ∀ x : ι → ℝ, (Set.pi Set.univ S).indicator
      (fun x => ENNReal.ofReal (densN s x)) x =
      ENNReal.ofReal (∏ i, (S i).indicator (dens1 s) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ S
    · rw [Set.indicator_of_mem hx]
      congr 1
      unfold densN
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ S i := by
        by_contra hcon
        push Not at hcon
        exact hx fun i _ => hcon i
      obtain ⟨i, hi⟩ := this
      have : ∏ i, (S i).indicator (dens1 s) (x i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      rw [this, ENNReal.ofReal_zero]
  simp_rw [hind]
  have hint : ∀ i, Integrable ((S i).indicator (dens1 s)) (gaussianReal 0 1) := fun i =>
    (integrable_dens1 hs).indicator (hS i)
  have hnn : ∀ i y, 0 ≤ (S i).indicator (dens1 s) y := fun i y =>
    Set.indicator_nonneg (fun y _ => (dens1_pos hs y).le) y
  have hI : Integrable (fun x : ι → ℝ => ∏ i, (S i).indicator (dens1 s) (x i)) (stdGauss ι) := by
    unfold stdGauss
    exact Integrable.fintype_prod_dep hint
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hnn i (x i))]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i => (S i).indicator (dens1 s)),
    ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg (hnn i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gauss1_density hs, withDensity_apply _ (hS i), integral_indicator (hS i),
    ofReal_integral_eq_lintegral_ofReal (integrable_dens1 hs).integrableOn
      (Filter.Eventually.of_forall fun y => (dens1_pos hs y).le)]

/-- `E g(s·γ) = E[g(γ)·densN s(γ)]`. -/
theorem integral_scale {s : ℝ} (hs : 0 < s) {g : (ι → ℝ) → ℝ} (hg : Measurable g) :
    ∫ x, g (s • x) ∂stdGauss ι = ∫ x, g x * densN s x ∂stdGauss ι := by
  rw [← integral_dens (stdGauss ι) (measurable_densN s) (densN_nonneg hs), ← stdGauss_scale hs,
    integral_map (measurable_const_smul s).aemeasurable hg.aestronglyMeasurable]

lemma integrable_densN {s : ℝ} (hs : 0 < s) : Integrable (densN (ι := ι) s) (stdGauss ι) := by
  unfold stdGauss densN
  exact Integrable.fintype_prod_dep fun _ => integrable_dens1 hs

lemma integral_densN {s : ℝ} (hs : 0 < s) : ∫ x, densN s x ∂stdGauss ι = 1 := by
  unfold stdGauss densN
  rw [integral_fintype_prod_eq_prod (fun _ : ι => dens1 s)]
  simp [integral_dens1 hs]

/-- **The affinity**: `E √(densN s) = (√(2s/(1 + s²)))^n`. -/
theorem aff_densN {s : ℝ} (hs : 0 < s) :
    ∫ x, rootN s x ∂stdGauss ι = √(2 * s / (1 + s ^ 2)) ^ Fintype.card ι := by
  unfold stdGauss rootN
  rw [integral_fintype_prod_eq_prod (fun _ : ι => root1 s)]
  simp [integral_root1 hs]

/-- **The Hellinger inequality for a change of scale.** For bounded measurable `g`:
`(E g(sγ) − E g(γ))² ≤ 2·(2 − 2(√(2s/(1 + s²)))^n)·(E g(sγ)² + E g(γ)²)`. -/
theorem gauss_scale_hell {s : ℝ} (hs : 0 < s) {g : (ι → ℝ) → ℝ} (hg : BM g) :
    (∫ x, g (s • x) ∂stdGauss ι - ∫ x, g x ∂stdGauss ι) ^ 2 ≤
      2 * (2 - 2 * √(2 * s / (1 + s ^ 2)) ^ Fintype.card ι) *
        (∫ x, g (s • x) ^ 2 ∂stdGauss ι + ∫ x, g x ^ 2 ∂stdGauss ι) := by
  obtain ⟨M, hM⟩ := hg.bdd
  have hM2 : ∀ x, g x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  have ia : Integrable (fun x : ι → ℝ => rootN s x ^ 2) (stdGauss ι) := by
    simp_rw [rootN_sq hs]; exact integrable_densN hs
  have ib : Integrable (fun _ : ι → ℝ => (1 : ℝ) ^ 2) (stdGauss ι) := integrable_const _
  have iha : Integrable (fun x : ι → ℝ => g x ^ 2 * rootN s x ^ 2) (stdGauss ι) := by
    simp_rw [rootN_sq hs]
    refine ((integrable_densN hs).const_mul (M ^ 2)).mono'
      ((hg.meas.pow_const 2).mul (measurable_densN s)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (densN_nonneg hs x))]
    exact mul_le_mul_of_nonneg_right (hM2 x) (densN_nonneg hs x)
  have ihb : Integrable (fun x : ι → ℝ => g x ^ 2 * (1 : ℝ) ^ 2) (stdGauss ι) := by
    simpa using hg.sq.integrable (stdGauss ι)
  have h := hell_core (stdGauss ι) (a := rootN s) (b := fun _ => 1) (h := g)
    (measurable_rootN s) measurable_const hg.meas ia ib iha ihb
  simp only [rootN_sq hs, one_pow, mul_one] at h
  rw [← integral_scale hs hg.meas, ← integral_scale hs (hg.meas.pow_const 2), integral_densN hs,
    aff_densN hs] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  have e : (1 : ℝ) + 1 - 2 * √(2 * s / (1 + s ^ 2)) ^ Fintype.card ι =
      2 - 2 * √(2 * s / (1 + s ^ 2)) ^ Fintype.card ι := by ring
  rw [e] at h
  exact h

/-! ## Two variances, one centre -/

/-- **The squared Hellinger distance of `N(c, τ²I_n)` and `N(c, τ₀²I_n)`**:
`2 − 2·(√(2ττ₀/(τ² + τ₀²)))^n`. -/
noncomputable def hellG (n : ℕ) (τ τ₀ : ℝ) : ℝ := 2 - 2 * √(2 * τ * τ₀ / (τ ^ 2 + τ₀ ^ 2)) ^ n

lemma hellG_le_two (n : ℕ) (τ τ₀ : ℝ) : hellG n τ τ₀ ≤ 2 := by
  unfold hellG
  have : 0 ≤ √(2 * τ * τ₀ / (τ ^ 2 + τ₀ ^ 2)) ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  linarith

lemma ratio_le_one (τ τ₀ : ℝ) : 2 * τ * τ₀ / (τ ^ 2 + τ₀ ^ 2) ≤ 1 := by
  by_cases h : τ ^ 2 + τ₀ ^ 2 = 0
  · rw [h, div_zero]; exact zero_le_one
  · have hpos : 0 < τ ^ 2 + τ₀ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [div_le_one hpos]
    nlinarith [sq_nonneg (τ - τ₀)]

lemma hellG_nonneg (n : ℕ) (τ τ₀ : ℝ) : 0 ≤ hellG n τ τ₀ := by
  unfold hellG
  have h1 : √(2 * τ * τ₀ / (τ ^ 2 + τ₀ ^ 2)) ≤ 1 :=
    Real.sqrt_le_one.mpr (ratio_le_one τ τ₀) |>.trans le_rfl
  have : √(2 * τ * τ₀ / (τ ^ 2 + τ₀ ^ 2)) ^ n ≤ 1 := pow_le_one₀ (Real.sqrt_nonneg _) h1
  linarith

/-- `1 − yⁿ ≤ (n/2)(1 − y²)` for `0 ≤ y ≤ 1` and `n ≥ 2`. -/
lemma one_sub_pow_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∀ n : ℕ, 2 ≤ n → 1 - y ^ n ≤ (n : ℝ) / 2 * (1 - y ^ 2) := by
  have step : ∀ k : ℕ, 1 - y ^ (k + 2) ≤ ((k + 2 : ℕ) : ℝ) / 2 * (1 - y ^ 2) ∧
      1 - y ^ (k + 3) ≤ ((k + 3 : ℕ) : ℝ) / 2 * (1 - y ^ 2) := by
    intro k
    induction k with
    | zero =>
      constructor
      · norm_num
      · norm_num
        nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1), sq_nonneg y,
          mul_nonneg (mul_nonneg hy0 hy0) (sub_nonneg.mpr hy1)]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h1 := ih.1
      have e : y ^ (k + 1 + 3) = y ^ 2 * y ^ (k + 2) := by ring
      rw [e]
      push_cast at h1 ⊢
      have hy2 : y ^ 2 ≤ 1 := pow_le_one₀ hy0 hy1
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg y)
      have h3 : y ^ 2 * (((k : ℝ) + 2) / 2 * (1 - y ^ 2)) ≤ ((k : ℝ) + 2) / 2 * (1 - y ^ 2) :=
        mul_le_of_le_one_left (mul_nonneg (by positivity) (sub_nonneg.mpr hy2)) hy2
      linarith
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact (step k).1

/-- **Lemma D3, the explicit bound**: for `n ≥ 2`, `τ ≥ 0`, `τ₀ > 0`:
`hellG n τ τ₀ ≤ n·(τ − τ₀)²/(τ² + τ₀²)`. -/
theorem hellG_le {n : ℕ} (hn : 2 ≤ n) {τ τ₀ : ℝ} (hτ : 0 ≤ τ) (hτ₀ : 0 < τ₀) :
    hellG n τ τ₀ ≤ (n : ℝ) * (τ - τ₀) ^ 2 / (τ ^ 2 + τ₀ ^ 2) := by
  unfold hellG
  have hpos : 0 < τ ^ 2 + τ₀ ^ 2 := by positivity
  have hx0 : 0 ≤ 2 * τ * τ₀ / (τ ^ 2 + τ₀ ^ 2) := by positivity
  have h1 := one_sub_pow_le (Real.sqrt_nonneg (2 * τ * τ₀ / (τ ^ 2 + τ₀ ^ 2)))
    (Real.sqrt_le_one.mpr (ratio_le_one τ τ₀)) n hn
  rw [Real.sq_sqrt hx0] at h1
  have e : (n : ℝ) * (τ - τ₀) ^ 2 / (τ ^ 2 + τ₀ ^ 2) =
      2 * ((n : ℝ) / 2 * (1 - 2 * τ * τ₀ / (τ ^ 2 + τ₀ ^ 2))) := by
    field_simp
    ring
  rw [e]
  linarith

/-- **The Hellinger inequality for two isotropic Gaussian vectors with one centre (item 2).**
`γ` standard Gaussian in `ℝ^ι` (`ι` not empty), `τ ≥ 0`, `τ₀ > 0`, `f` bounded measurable:
`(E f(c + τγ) − E f(c + τ₀γ))² ≤ 2·hellG n τ τ₀·(E f(c + τγ)² + E f(c + τ₀γ)²)`. -/
theorem gaussScale138 (hι : 0 < Fintype.card ι) (c : ι → ℝ) {τ τ₀ : ℝ} (hτ : 0 ≤ τ)
    (hτ₀ : 0 < τ₀) {f : (ι → ℝ) → ℝ} (hf : BM f) :
    (∫ x, f (c + τ • x) ∂stdGauss ι - ∫ x, f (c + τ₀ • x) ∂stdGauss ι) ^ 2 ≤
      2 * hellG (Fintype.card ι) τ τ₀ *
        (∫ x, f (c + τ • x) ^ 2 ∂stdGauss ι + ∫ x, f (c + τ₀ • x) ^ 2 ∂stdGauss ι) := by
  have mτ : ∀ t : ℝ, Measurable (fun x : ι → ℝ => c + t • x) := fun t =>
    measurable_const.add (measurable_const_smul t)
  rcases hτ.eq_or_lt with h0 | hpos
  · -- `τ = 0`: the trivial bound
    subst h0
    have hH : hellG (Fintype.card ι) 0 τ₀ = 2 := by
      unfold hellG
      simp [zero_pow hι.ne']
    rw [hH]
    have b1 : BM (fun x : ι → ℝ => f (c + (0 : ℝ) • x)) := hf.comp (mτ 0)
    have b2 : BM (fun x : ι → ℝ => f (c + τ₀ • x)) := hf.comp (mτ τ₀)
    have j1 := sq_integral_le (ρ := stdGauss ι) (b1.sq.integrable _)
    have j2 := sq_integral_le (ρ := stdGauss ι) (b2.sq.integrable _)
    nlinarith [sq_nonneg (∫ x, f (c + (0 : ℝ) • x) ∂stdGauss ι + ∫ x, f (c + τ₀ • x) ∂stdGauss ι)]
  · set g : (ι → ℝ) → ℝ := fun x => f (c + τ₀ • x) with hgdef
    have hg : BM g := hf.comp (mτ τ₀)
    have hs : 0 < τ / τ₀ := div_pos hpos hτ₀
    have h := gauss_scale_hell hs hg
    have e1 : ∀ x : ι → ℝ, g ((τ / τ₀) • x) = f (c + τ • x) := by
      intro x
      simp only [hgdef]
      congr 2
      rw [smul_smul]
      congr 1
      field_simp
    have e2 : 2 * (τ / τ₀) / (1 + (τ / τ₀) ^ 2) = 2 * τ * τ₀ / (τ ^ 2 + τ₀ ^ 2) := by
      field_simp
      ring
    simp only [e1, e2] at h
    exact h

end BstLean.Part138

open BstLean.Part138 in
#print axioms stdGauss_scale
open BstLean.Part138 in
#print axioms gaussScale138
open BstLean.Part138 in
#print axioms hellG_le
