import BstLean.Part138Mix

/-!
# Part 141: the Hellinger distance of two isotropic Gaussian vectors with one scale and two centres

Role: `delegations/statements/p141-spec.md`. This file is the analogue of `Part138Gauss` (a change
of scale) for a change of CENTRE (a shift).

`γ` is a standard Gaussian vector of `ℝ^ι` (`stdGauss ι`), `d ∈ ℝ^ι`.

* `densS1 d`: the density of `N(d, 1)` with respect to `N(0, 1)` on `ℝ`; `gaussS1_density`.
* `densSN d`: the density of `γ + d` with respect to `γ` (a product); `stdGauss_shift`.
* `integral_shift`: `E g(γ + d) = E[g(γ)·densSN d(γ)]`.
* `aff_densSN`: the affinity `E √(densSN d(γ)) = exp(−|d|²/8)`.
* **`gaussShift141`**: for bounded measurable `g`:
  `(E g(γ + d) − E g(γ))² ≤ 2·(2 − 2·exp(−|d|²/8))·(E g(γ + d)² + E g(γ)²)`.
* **`cheapShift141`**: two cheap stand-ins with one scalar `τ > 0` and two centres:
  `(E_{ν′(c′, τ)} φ − E_{ν′(c, τ)} φ)² ≤ |c′ − c|²/(2τ²)·(E_{ν′(c′, τ)} φ² + E_{ν′(c, τ)} φ²)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part138

/-! ## One coordinate -/

/-- The density of `N(d, 1)` with respect to `N(0, 1)`. -/
noncomputable def densS1 (d y : ℝ) : ℝ := rexp (d * y - d ^ 2 / 2)

/-- The square root of `densS1`. -/
noncomputable def rootS1 (d y : ℝ) : ℝ := rexp ((d * y - d ^ 2 / 2) / 2)

lemma densS1_pos (d y : ℝ) : 0 < densS1 d y := Real.exp_pos _

lemma rootS1_nonneg (d y : ℝ) : 0 ≤ rootS1 d y := (Real.exp_pos _).le

lemma rootS1_sq (d y : ℝ) : rootS1 d y ^ 2 = densS1 d y := by
  unfold rootS1 densS1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma measurable_densS1 (d : ℝ) : Measurable (densS1 d) := by
  unfold densS1
  exact (((measurable_const_mul d).sub_const _)).exp

lemma measurable_rootS1 (d : ℝ) : Measurable (rootS1 d) := by
  unfold rootS1
  exact ((((measurable_const_mul d).sub_const _)).div_const _).exp

/-- `N(d, 1) = densS1 d · N(0, 1)`. -/
lemma gaussS1_density (d : ℝ) :
    gaussianReal d 1 =
      (gaussianReal 0 1).withDensity (fun y => ENNReal.ofReal (densS1 d y)) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) (measurable_densS1 d).ennreal_ofReal]
  congr 1
  funext y
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, densS1, NNReal.coe_one, sub_zero, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma integrable_densS1 (d : ℝ) : Integrable (densS1 d) (gaussianReal 0 1) := by
  refine ⟨(measurable_densS1 d).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y => (densS1_pos d y).le)]
  have h : ∫⁻ y, ENNReal.ofReal (densS1 d y) ∂gaussianReal 0 1 =
      ((gaussianReal 0 1).withDensity (fun y => ENNReal.ofReal (densS1 d y))) Set.univ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [h, ← gaussS1_density d, measure_univ]
  exact ENNReal.one_lt_top

lemma integral_densS1 (d : ℝ) : ∫ y, densS1 d y ∂gaussianReal 0 1 = 1 := by
  have h : ∫⁻ y, ENNReal.ofReal (densS1 d y) ∂gaussianReal 0 1 = 1 := by
    have h' : ∫⁻ y, ENNReal.ofReal (densS1 d y) ∂gaussianReal 0 1 =
        ((gaussianReal 0 1).withDensity (fun y => ENNReal.ofReal (densS1 d y))) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h', ← gaussS1_density d, measure_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_densS1 d)
    (Filter.Eventually.of_forall fun y => (densS1_pos d y).le), ← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun y => (densS1_pos d y).le)
    zero_le_one).mp h

/-- The affinity in one coordinate: `E √(densS1 d) = exp(−d²/8)`. -/
lemma integral_rootS1 (d : ℝ) :
    ∫ y, rootS1 d y ∂gaussianReal 0 1 = rexp (-(d ^ 2) / 8) := by
  have e : ∀ y, rootS1 d y = rexp (-(d ^ 2) / 8) * densS1 (d / 2) y := by
    intro y
    unfold rootS1 densS1
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_densS1, mul_one]

/-! ## The vector -/

variable {ι : Type*} [Fintype ι]

/-- The density of `γ + d` with respect to `γ`. -/
noncomputable def densSN (d : ι → ℝ) (x : ι → ℝ) : ℝ := ∏ i, densS1 (d i) (x i)

/-- The square root of `densSN`. -/
noncomputable def rootSN (d : ι → ℝ) (x : ι → ℝ) : ℝ := ∏ i, rootS1 (d i) (x i)

lemma densSN_nonneg (d x : ι → ℝ) : 0 ≤ densSN d x :=
  Finset.prod_nonneg fun i _ => (densS1_pos (d i) (x i)).le

lemma rootSN_nonneg (d x : ι → ℝ) : 0 ≤ rootSN d x :=
  Finset.prod_nonneg fun i _ => rootS1_nonneg (d i) (x i)

lemma rootSN_sq (d x : ι → ℝ) : rootSN d x ^ 2 = densSN d x := by
  unfold rootSN densSN
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => rootS1_sq (d i) (x i)

lemma measurable_densSN (d : ι → ℝ) : Measurable (densSN d) := by
  unfold densSN
  exact Finset.measurable_prod _ fun i _ => (measurable_densS1 (d i)).comp (measurable_pi_apply i)

lemma measurable_rootSN (d : ι → ℝ) : Measurable (rootSN d) := by
  unfold rootSN
  exact Finset.measurable_prod _ fun i _ => (measurable_rootS1 (d i)).comp (measurable_pi_apply i)

/-- **The distribution of `γ + d` has the density `densSN d` with respect to `γ`.** -/
theorem stdGauss_shift (d : ι → ℝ) :
    (stdGauss ι).map (fun x => x + d) =
      (stdGauss ι).withDensity (fun x => ENNReal.ofReal (∏ i, densS1 (d i) (x i))) := by
  classical
  have e1 : (stdGauss ι).map (fun x => x + d) =
      Measure.pi (fun i : ι => gaussianReal (d i) 1) := by
    unfold stdGauss
    have h := Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
      (f := fun i : ι => fun y : ℝ => y + d i)
      (hμ := fun _ => by rw [gaussianReal_map_add_const]; infer_instance)
      (fun i => (measurable_add_const (d i)).aemeasurable)
    have h2 : (fun x : ι → ℝ => x + d) = fun x i => x i + d i := by
      funext x i; simp
    rw [h2, h]
    congr 1
    funext i
    rw [gaussianReal_map_add_const, zero_add]
  rw [e1]
  refine Measure.pi_eq fun S hS => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS),
    ← lintegral_indicator (MeasurableSet.univ_pi hS)]
  have hind : ∀ x : ι → ℝ, (Set.pi Set.univ S).indicator
      (fun x => ENNReal.ofReal (∏ i, densS1 (d i) (x i))) x =
      ENNReal.ofReal (∏ i, (S i).indicator (densS1 (d i)) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ S
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ S i := by
        by_contra hcon
        push Not at hcon
        exact hx fun i _ => hcon i
      obtain ⟨i, hi⟩ := this
      have : ∏ i, (S i).indicator (densS1 (d i)) (x i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      rw [this, ENNReal.ofReal_zero]
  simp_rw [hind]
  have hint : ∀ i, Integrable ((S i).indicator (densS1 (d i))) (gaussianReal 0 1) := fun i =>
    (integrable_densS1 (d i)).indicator (hS i)
  have hnn : ∀ i y, 0 ≤ (S i).indicator (densS1 (d i)) y := fun i y =>
    Set.indicator_nonneg (fun y _ => (densS1_pos (d i) y).le) y
  have hI : Integrable (fun x : ι → ℝ => ∏ i, (S i).indicator (densS1 (d i)) (x i))
      (stdGauss ι) := by
    unfold stdGauss
    exact Integrable.fintype_prod_dep hint
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hnn i (x i))]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i => (S i).indicator (densS1 (d i))),
    ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg (hnn i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussS1_density (d i), withDensity_apply _ (hS i), integral_indicator (hS i),
    ofReal_integral_eq_lintegral_ofReal (integrable_densS1 (d i)).integrableOn
      (Filter.Eventually.of_forall fun y => (densS1_pos (d i) y).le)]

/-- `E g(γ + d) = E[g(γ)·densSN d(γ)]`. -/
theorem integral_shift (d : ι → ℝ) {g : (ι → ℝ) → ℝ} (hg : Measurable g) :
    ∫ x, g (x + d) ∂stdGauss ι = ∫ x, g x * densSN d x ∂stdGauss ι := by
  rw [← integral_dens (stdGauss ι) (measurable_densSN d) (densSN_nonneg d)]
  have h := stdGauss_shift d
  change _ = (stdGauss ι).withDensity (fun x => ENNReal.ofReal (densSN d x)) at h
  rw [← h, integral_map (measurable_add_const d).aemeasurable hg.aestronglyMeasurable]

lemma integrable_densSN (d : ι → ℝ) : Integrable (densSN d) (stdGauss ι) := by
  unfold stdGauss densSN
  exact Integrable.fintype_prod_dep fun i => integrable_densS1 (d i)

lemma integral_densSN (d : ι → ℝ) : ∫ x, densSN d x ∂stdGauss ι = 1 := by
  unfold stdGauss densSN
  rw [integral_fintype_prod_eq_prod (fun i : ι => densS1 (d i))]
  simp [integral_densS1]

/-- **The affinity**: `E √(densSN d) = exp(−|d|²/8)`. -/
theorem aff_densSN (d : ι → ℝ) :
    ∫ x, rootSN d x ∂stdGauss ι = rexp (-(∑ i, d i ^ 2) / 8) := by
  unfold stdGauss rootSN
  rw [integral_fintype_prod_eq_prod (fun i : ι => rootS1 (d i))]
  simp_rw [integral_rootS1]
  rw [← Real.exp_sum]
  congr 1
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The Hellinger inequality for a change of centre.** For bounded measurable `g`:
`(E g(γ + d) − E g(γ))² ≤ 2·(2 − 2·exp(−|d|²/8))·(E g(γ + d)² + E g(γ)²)`. -/
theorem gaussShift141 (d : ι → ℝ) {g : (ι → ℝ) → ℝ} (hg : BM g) :
    (∫ x, g (x + d) ∂stdGauss ι - ∫ x, g x ∂stdGauss ι) ^ 2 ≤
      2 * (2 - 2 * rexp (-(∑ i, d i ^ 2) / 8)) *
        (∫ x, g (x + d) ^ 2 ∂stdGauss ι + ∫ x, g x ^ 2 ∂stdGauss ι) := by
  obtain ⟨M, hM⟩ := hg.bdd
  have hM2 : ∀ x, g x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  have ia : Integrable (fun x : ι → ℝ => rootSN d x ^ 2) (stdGauss ι) := by
    simp_rw [rootSN_sq]; exact integrable_densSN d
  have ib : Integrable (fun _ : ι → ℝ => (1 : ℝ) ^ 2) (stdGauss ι) := integrable_const _
  have iha : Integrable (fun x : ι → ℝ => g x ^ 2 * rootSN d x ^ 2) (stdGauss ι) := by
    simp_rw [rootSN_sq]
    refine ((integrable_densSN d).const_mul (M ^ 2)).mono'
      ((hg.meas.pow_const 2).mul (measurable_densSN d)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (densSN_nonneg d x))]
    exact mul_le_mul_of_nonneg_right (hM2 x) (densSN_nonneg d x)
  have ihb : Integrable (fun x : ι → ℝ => g x ^ 2 * (1 : ℝ) ^ 2) (stdGauss ι) := by
    simpa using hg.sq.integrable (stdGauss ι)
  have h := hell_core (stdGauss ι) (a := rootSN d) (b := fun _ => 1) (h := g)
    (measurable_rootSN d) measurable_const hg.meas ia ib iha ihb
  simp only [rootSN_sq, one_pow, mul_one] at h
  rw [← integral_shift d hg.meas, ← integral_shift d (hg.meas.pow_const 2), integral_densSN d,
    aff_densSN d] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  have e : (1 : ℝ) + 1 - 2 * rexp (-(∑ i, d i ^ 2) / 8) =
      2 - 2 * rexp (-(∑ i, d i ^ 2) / 8) := by ring
  rw [e] at h
  exact h

/-! ## Two centres, one scalar: the cheap stand-ins -/

/-- **The cheap stand-ins with two centres and one scalar.** For `τ > 0` and bounded measurable
`φ`: `(E_{ν′(c′, τ)} φ − E_{ν′(c, τ)} φ)² ≤
  |c′ − c|²/(2τ²)·(E_{ν′(c′, τ)} φ² + E_{ν′(c, τ)} φ²)`. -/
theorem cheapShift141 {n : ℕ} (c c' : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    (∫ x, φ x ∂cheapIn c' τ - ∫ x, φ x ∂cheapIn c τ) ^ 2 ≤
      normSq (c' - c) / (2 * τ ^ 2) *
        (∫ x, φ x ^ 2 ∂cheapIn c' τ + ∫ x, φ x ^ 2 ∂cheapIn c τ) := by
  set d : Fin n → ℝ := τ⁻¹ • (c' - c) with hd
  set g : (Fin n → ℝ) → ℝ := fun x => φ (sphPt (c + τ • x)) with hg
  have bg : BM g :=
    hφ.comp (measurable_sphPt.comp (measurable_const.add (measurable_const_smul τ)))
  have e1 : ∀ x : Fin n → ℝ, c' + τ • x = c + τ • (x + d) := by
    intro x
    rw [hd, smul_add, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
    abel
  have h := gaussShift141 d bg
  rw [integral_cheapIn c' τ hφ.meas, integral_cheapIn c τ hφ.meas,
    integral_cheapIn c' τ (hφ.meas.pow_const 2), integral_cheapIn c τ (hφ.meas.pow_const 2)]
  simp_rw [e1]
  have hsum : ∑ i, d i ^ 2 = normSq (c' - c) / τ ^ 2 := by
    unfold normSq
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hd, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hexp : 2 * (2 - 2 * rexp (-(∑ i, d i ^ 2) / 8)) ≤ normSq (c' - c) / (2 * τ ^ 2) := by
    have h1 := Real.add_one_le_exp (-(∑ i, d i ^ 2) / 8)
    have h2 : normSq (c' - c) / (2 * τ ^ 2) = (∑ i, d i ^ 2) / 2 := by
      rw [hsum]; field_simp
    rw [h2]
    linarith
  have hI : 0 ≤ ∫ x, g (x + d) ^ 2 ∂stdGauss (Fin n) + ∫ x, g x ^ 2 ∂stdGauss (Fin n) :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  exact h.trans (mul_le_mul_of_nonneg_right hexp hI)

end BstLean.Part141

open BstLean.Part141 in
#print axioms stdGauss_shift
open BstLean.Part141 in
#print axioms integral_shift
open BstLean.Part141 in
#print axioms aff_densSN
open BstLean.Part141 in
#print axioms gaussShift141
open BstLean.Part141 in
#print axioms cheapShift141
