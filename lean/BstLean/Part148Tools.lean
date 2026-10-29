import BstLean.Part109Gram
import BstLean.Part132Rows
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.ProductMeasure

/-!
# Part 148 (file `Tools`): exponential lower tails for sums of independent terms

Role: `delegations/statements/p148-spec.md`, the tools of item 1. No paper source: these are
standard Chernoff bounds, written for this project.

* `chernoffLower`: independent `X_i` with `E exp(−s·X_i) ≤ exp(−s·a_i + s²·b_i/2)` for every
  `s ≥ 0`, and `Σ b_i ≤ B`: `Pr(Σ X_i ≤ Σ a_i − t) ≤ exp(−t²/(2B))`.
* `expLowerTail_indep`: independent NONNEGATIVE `X_i` with finite second moments:
  `Pr(Σ X_i ≤ Σ E X_i − t) ≤ exp(−t²/(2·Σ E X_i²))`. No fourth moment is necessary.
* `expLowerTail_pi`: the same for `Σ_i f(ω_i)` under a product of copies of one distribution.
* `gaussMat_rows_map`: the rows of a Gaussian matrix are independent: the distribution of the
  family of rows is the product of the distributions of the rows.
* `expLowerTail_rows`: the same for `Σ_i f(row_i M)`, `M` a Gaussian matrix.
* `chiSqLower`: `Pr(Σ λ_i ξ_i² ≤ Σ λ_i − t) ≤ exp(−t²/(4B))` for `λ_i ≥ 0`, `Σ λ_i² ≤ B`, `ξ` a
  standard Gaussian vector (the exact variance `2·Σ λ_i²` is the proxy).
* `qformLower`: for a symmetric positive semidefinite matrix `C` and `Σ_{ij} C_{ij}² ≤ B`:
  `Pr(ξᵀCξ ≤ tr C − t) ≤ exp(−t²/(4B))`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part148

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132

/-! ## The Chernoff bound for a lower tail -/

/-- **The Chernoff bound for the lower tail of a sum of independent variables.** If
`E exp(−s·X_i) ≤ exp(−s·a_i + s²·b_i/2)` for every `s ≥ 0` and `Σ b_i ≤ B`, then
`Pr(Σ X_i ≤ Σ a_i − t) ≤ exp(−t²/(2B))` for `t ≥ 0`. -/
theorem chernoffLower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) {a b : ι → ℝ}
    (hint : ∀ i (s : ℝ), 0 ≤ s → Integrable (fun ω => exp (-s * X i ω)) μ)
    (hmgf : ∀ i (s : ℝ), 0 ≤ s → mgf (X i) μ (-s) ≤ exp (-s * a i + s ^ 2 * b i / 2))
    {B : ℝ} (hB : ∑ i, b i ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i, X i ω ≤ ∑ i, a i - t} ≤ exp (-t ^ 2 / (2 * B)) := by
  rcases le_or_gt B 0 with hB0 | hB0
  · have h1 : (0 : ℝ) ≤ -t ^ 2 / (2 * B) :=
      div_nonneg_of_nonpos (by nlinarith) (by linarith)
    exact measureReal_le_one.trans (Real.one_le_exp h1)
  set s : ℝ := t / B with hs
  have hs0 : 0 ≤ s := div_nonneg ht hB0.le
  have hfun : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω; simp
  have hI : Integrable (fun ω => exp (-s * (∑ i, X i) ω)) μ :=
    hind.integrable_exp_mul_sum hm (s := Finset.univ) fun i _ => hint i s hs0
  have h := measure_le_le_exp_mul_mgf (μ := μ) (X := ∑ i, X i) (t := -s) (∑ i, a i - t)
    (by linarith) hI
  have hset : {ω | (∑ i, X i) ω ≤ ∑ i, a i - t} = {ω | ∑ i, X i ω ≤ ∑ i, a i - t} := by
    ext ω; simp
  rw [hset] at h
  refine h.trans ?_
  rw [hind.mgf_sum hm Finset.univ]
  have hprod : ∏ i, mgf (X i) μ (-s) ≤ ∏ i, exp (-s * a i + s ^ 2 * b i / 2) :=
    Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) fun i _ => hmgf i s hs0
  have hexp : ∏ i, exp (-s * a i + s ^ 2 * b i / 2) =
      exp (-s * ∑ i, a i + s ^ 2 * (∑ i, b i) / 2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  calc exp (- -s * (∑ i, a i - t)) * ∏ i, mgf (X i) μ (-s)
      ≤ exp (- -s * (∑ i, a i - t)) * exp (-s * ∑ i, a i + s ^ 2 * (∑ i, b i) / 2) := by
        rw [← hexp]
        exact mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = exp (-s * t + s ^ 2 * (∑ i, b i) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ exp (-t ^ 2 / (2 * B)) := by
        apply Real.exp_le_exp.mpr
        have h2 : s ^ 2 * (∑ i, b i) / 2 ≤ s ^ 2 * B / 2 := by
          have := mul_le_mul_of_nonneg_left hB (sq_nonneg s)
          linarith
        have e : -s * t + s ^ 2 * B / 2 = -t ^ 2 / (2 * B) := by
          rw [hs]
          field_simp
          ring
        linarith

/-- `e^{−u} ≤ 1 − u + u²/2` for `u ≥ 0`. -/
lemma exp_neg_le_quad {u : ℝ} (hu : 0 ≤ u) : exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg hu
  have hp : 0 < 1 + u + u ^ 2 / 2 := by positivity
  rw [Real.exp_neg]
  calc (exp u)⁻¹ ≤ (1 + u + u ^ 2 / 2)⁻¹ := inv_anti₀ hp h1
    _ ≤ 1 - u + u ^ 2 / 2 := by
        rw [inv_le_iff_one_le_mul₀ hp]
        nlinarith [sq_nonneg (u ^ 2)]

/-- The mean of `e^{−sX}` for a nonnegative `X` with a finite second moment. -/
lemma mgf_neg_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hpos : ∀ ω, 0 ≤ X ω)
    (h2 : Integrable (fun ω => X ω ^ 2) μ) {s : ℝ} (hs : 0 ≤ s) :
    Integrable X μ ∧ Integrable (fun ω => exp (-s * X ω)) μ ∧
      mgf X μ (-s) ≤ exp (-s * ∫ ω, X ω ∂μ + s ^ 2 * (∫ ω, X ω ^ 2 ∂μ) / 2) := by
  have h1 : Integrable X μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add h2) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos ω)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (X ω - 1)]
  have hE : Integrable (fun ω => exp (-s * X ω)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((measurable_const.mul hm).exp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [hpos ω])
  refine ⟨h1, hE, ?_⟩
  have hq : Integrable (fun ω => 1 - s * X ω + s ^ 2 * X ω ^ 2 / 2) μ :=
    ((integrable_const (1 : ℝ)).sub (h1.const_mul s)).add ((h2.const_mul (s ^ 2)).div_const 2)
  have hle : mgf X μ (-s) ≤ ∫ ω, (1 - s * X ω + s ^ 2 * X ω ^ 2 / 2) ∂μ := by
    unfold mgf
    refine integral_mono hE hq fun ω => ?_
    have h := exp_neg_le_quad (mul_nonneg hs (hpos ω))
    have e1 : -s * X ω = -(s * X ω) := by ring
    rw [e1]
    refine h.trans (le_of_eq ?_)
    ring
  have hval : ∫ ω, (1 - s * X ω + s ^ 2 * X ω ^ 2 / 2) ∂μ =
      1 - s * ∫ ω, X ω ∂μ + s ^ 2 * (∫ ω, X ω ^ 2 ∂μ) / 2 := by
    have e : (fun ω => 1 - s * X ω + s ^ 2 * X ω ^ 2 / 2) =
        fun ω => (1 - s * X ω) + s ^ 2 / 2 * X ω ^ 2 := by
      funext ω; ring
    have hA : Integrable (fun ω => 1 - s * X ω) μ :=
      (integrable_const (1 : ℝ)).sub (h1.const_mul s)
    have hA2 : Integrable (fun ω => s * X ω) μ := h1.const_mul s
    have hB2 : Integrable (fun ω => s ^ 2 / 2 * X ω ^ 2) μ := h2.const_mul (s ^ 2 / 2)
    rw [e, integral_add hA hB2, integral_sub (integrable_const (1 : ℝ)) hA2,
      integral_const_mul, integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [hval] at hle
  refine hle.trans ?_
  have := Real.add_one_le_exp (-s * ∫ ω, X ω ∂μ + s ^ 2 * (∫ ω, X ω ^ 2 ∂μ) / 2)
  linarith

/-- **An exponential lower tail for a sum of independent nonnegative variables with finite
second moments**: `Pr(Σ X_i ≤ Σ E X_i − t) ≤ exp(−t²/(2B))` if `Σ E X_i² ≤ B`, `t ≥ 0`. -/
theorem expLowerTail_indep {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (hpos : ∀ i ω, 0 ≤ X i ω)
    (h2 : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    {B : ℝ} (hB : ∑ i, ∫ ω, X i ω ^ 2 ∂μ ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i, X i ω ≤ ∑ i, ∫ ω, X i ω ∂μ - t} ≤ exp (-t ^ 2 / (2 * B)) :=
  chernoffLower hind hm (a := fun i => ∫ ω, X i ω ∂μ) (b := fun i => ∫ ω, X i ω ^ 2 ∂μ)
    (fun i _ hs => (mgf_neg_le (hm i) (hpos i) (h2 i) hs).2.1)
    (fun i _ hs => (mgf_neg_le (hm i) (hpos i) (h2 i) hs).2.2) hB ht

/-- **The same for a sum `Σ_i f(ω_i)` under a product of copies of one distribution `ρ`**:
`Pr(Σ_i f(ω_i) ≤ N·E f − t) ≤ exp(−t²/(2B))` if `N·E f² ≤ B`, `f ≥ 0`, `t ≥ 0`. -/
theorem expLowerTail_pi {E ι : Type*} [MeasurableSpace E] [Fintype ι] (ρ : Measure E)
    [IsProbabilityMeasure ρ] {f : E → ℝ} (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (h2 : Integrable (fun x => f x ^ 2) ρ)
    {B : ℝ} (hB : (Fintype.card ι : ℝ) * ∫ x, f x ^ 2 ∂ρ ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : ι => ρ).real
      {ω | ∑ i, f (ω i) ≤ (Fintype.card ι : ℝ) * ∫ x, f x ∂ρ - t} ≤ exp (-t ^ 2 / (2 * B)) := by
  have hind := iIndepFun_pi (μ := fun _ : ι => ρ) (X := fun _ => f) (fun _ => hf.aemeasurable)
  have hm : ∀ i : ι, Measurable (fun ω : ι → E => f (ω i)) := fun i =>
    hf.comp (measurable_pi_apply i)
  have h2' : ∀ i : ι, Integrable (fun ω : ι → E => f (ω i) ^ 2) (Measure.pi fun _ : ι => ρ) :=
    fun i => integrable_comp_eval (μ := fun _ : ι => ρ) (i := i) h2
  have e2 : ∀ i : ι, ∫ ω : ι → E, f (ω i) ^ 2 ∂(Measure.pi fun _ : ι => ρ) = ∫ x, f x ^ 2 ∂ρ :=
    fun i => integral_comp_eval (μ := fun _ : ι => ρ) (i := i) h2.aestronglyMeasurable
  have e1 : ∀ i : ι, ∫ ω : ι → E, f (ω i) ∂(Measure.pi fun _ : ι => ρ) = ∫ x, f x ∂ρ :=
    fun i => integral_comp_eval (μ := fun _ : ι => ρ) (i := i) hf.aestronglyMeasurable
  have h := expLowerTail_indep hind hm (fun i ω => hpos (ω i)) h2' (B := B)
    (by simp only [e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; exact hB) ht
  simp only [e1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact h

/-! ## The rows of a Gaussian matrix -/

/-- **The rows of a Gaussian matrix are independent**: the distribution of the family of rows
is the product of the distributions of the rows. -/
theorem gaussMat_rows_map (m k : ℕ) (v : ℝ) :
    (gaussMat m k v).map (fun M i => rowOf i M) =
      Measure.pi fun _ : Fin m => (stdGauss (Fin k)).map (fun ξ => Real.sqrt v • ξ) := by
  have hcur : (stdGauss (Fin m × Fin k)).map (MeasurableEquiv.curry (Fin m) (Fin k) ℝ) =
      Measure.pi fun _ : Fin m => stdGauss (Fin k) := by
    have h := Measure.infinitePi_map_curry
      (μ := fun (_ : Fin m) (_ : Fin k) => gaussianReal 0 1)
    simp only [Measure.infinitePi_eq_pi] at h
    exact h
  have hm1 : Measurable (fun ζ : Fin m → Fin k → ℝ => fun i => Real.sqrt v • ζ i) :=
    measurable_pi_iff.mpr fun i => (measurable_const_smul _).comp (measurable_pi_apply i)
  have hrows : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => fun i => rowOf i M) :=
    measurable_pi_iff.mpr fun i => measurable_rowOf i
  have h2 := Measure.pi_map_pi (μ := fun _ : Fin m => stdGauss (Fin k))
    (f := fun _ => fun ξ : Fin k → ℝ => Real.sqrt v • ξ)
    (fun _ => (measurable_const_smul _).aemeasurable)
  rw [← h2, ← hcur, Measure.map_map hm1 (MeasurableEquiv.measurable _)]
  unfold gaussMat
  rw [Measure.map_map hrows (measurable_ofFlat _)]
  rfl

/-- **An exponential lower tail for a sum of a nonnegative function of the rows of a Gaussian
matrix**: `Pr(Σ_i f(row_i M) ≤ m·E f − t) ≤ exp(−t²/(2B))` if `m·E f² ≤ B`; the means are over
one row, `√v·ξ` with `ξ` a standard Gaussian vector. -/
theorem expLowerTail_rows {m k : ℕ} (v : ℝ) {f : (Fin k → ℝ) → ℝ} (hf : Measurable f)
    (hpos : ∀ x, 0 ≤ f x)
    (h2 : Integrable (fun ξ => f (Real.sqrt v • ξ) ^ 2) (stdGauss (Fin k)))
    {B : ℝ} (hB : (m : ℝ) * ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    (gaussMat m k v).real
      {M | ∑ i, f (rowOf i M) ≤ (m : ℝ) * ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) - t} ≤
      exp (-t ^ 2 / (2 * B)) := by
  set ρ : Measure (Fin k → ℝ) := (stdGauss (Fin k)).map (fun ξ => Real.sqrt v • ξ) with hρ
  have hsm : Measurable (fun ξ : Fin k → ℝ => Real.sqrt v • ξ) := measurable_const_smul _
  have : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff hsm.aemeasurable).mpr inferInstance
  have e1 : ∫ x, f x ∂ρ = ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) :=
    integral_map hsm.aemeasurable hf.aestronglyMeasurable
  have e2 : ∫ x, f x ^ 2 ∂ρ = ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) :=
    integral_map hsm.aemeasurable (hf.pow_const 2).aestronglyMeasurable
  have h2' : Integrable (fun x => f x ^ 2) ρ :=
    (integrable_map_measure (hf.pow_const 2).aestronglyMeasurable hsm.aemeasurable).mpr h2
  have h := expLowerTail_pi (ι := Fin m) ρ hf hpos h2' (B := B)
    (by rw [e2, Fintype.card_fin]; exact hB) ht
  rw [e1, Fintype.card_fin, ← gaussMat_rows_map] at h
  have hrows : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => fun i => rowOf i M) :=
    measurable_pi_iff.mpr fun i => measurable_rowOf i
  have hS : MeasurableSet {ω : Fin m → Fin k → ℝ |
      ∑ i, f (ω i) ≤ (m : ℝ) * ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) - t} :=
    measurableSet_le (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i))
      measurable_const
  rw [map_measureReal_apply hrows hS] at h
  exact h

/-! ## Squares of Gaussians and a positive semidefinite quadratic form -/

/-- `∫ e^{−t z²} dγ(z) = (1 + 2t)^{−1/2}` for `t ≥ 0`. -/
lemma gauss_laplace_sq {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun z : ℝ => exp (-t * z ^ 2)) (gaussianReal 0 1) ∧
    (∫ z : ℝ, exp (-t * z ^ 2) ∂gaussianReal 0 1) = (Real.sqrt (1 + 2 * t))⁻¹ := by
  constructor
  · refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
  · rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    have he : (fun z : ℝ => gaussianPDFReal 0 1 z • exp (-t * z ^ 2)) =
        fun z => (Real.sqrt (2 * π))⁻¹ * exp (-(1 / 2 + t) * z ^ 2) := by
      funext z
      simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,
        mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [he, integral_const_mul, integral_gaussian]
    have hp := Real.pi_pos
    have ht' : 0 < 1 + 2 * t := by linarith
    have hdiv : π / (1 / 2 + t) = (2 * π) / (1 + 2 * t) := by
      field_simp
    rw [hdiv, Real.sqrt_div (by positivity), div_eq_mul_inv]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- `(1 + y)·e^{−y + y²/2} ≥ 1` for `y ≥ 0`. -/
lemma one_le_mul_exp {y : ℝ} (hy : 0 ≤ y) : 1 ≤ (1 + y) * exp (-y + y ^ 2 / 2) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => (1 + y) * exp (-y + y ^ 2 / 2))
      (y ^ 2 * exp (-y + y ^ 2 / 2)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := (hasDerivAt_id' y).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => -y + y ^ 2 / 2) (-1 + y) y := by
      have ha : HasDerivAt (fun y : ℝ => -y) (-1) y := (hasDerivAt_id' y).neg
      have hb : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
        have := (hasDerivAt_pow 2 y).div_const 2
        convert this using 1
        norm_num
      exact ha.add hb
    have h3 : HasDerivAt (fun y : ℝ => exp (-y + y ^ 2 / 2))
        (exp (-y + y ^ 2 / 2) * (-1 + y)) y := h2.exp
    have := h1.mul h3
    convert this using 1
    ring
  have hmono : MonotoneOn (fun y : ℝ => (1 + y) * exp (-y + y ^ 2 / 2)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.2 fun y => (hd y).continuousAt).continuousOn
    · intro y _
      exact (hd y).differentiableAt.differentiableWithinAt
    · intro y _
      rw [(hd y).deriv]
      positivity
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simpa using h

/-- `(1 + 2x)^{−1/2} ≤ e^{−x + x²}` for `x ≥ 0`. -/
lemma inv_sqrt_le_exp {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (1 + 2 * x))⁻¹ ≤ exp (-x + x ^ 2) := by
  have h := one_le_mul_exp (y := 2 * x) (by linarith)
  have hpos : 0 < 1 + 2 * x := by linarith
  have hs : 0 < Real.sqrt (1 + 2 * x) := Real.sqrt_pos.mpr hpos
  rw [inv_le_iff_one_le_mul₀ hs]
  have e : exp (-(2 * x) + (2 * x) ^ 2 / 2) = exp (-x + x ^ 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e] at h
  have hE := exp_pos (-x + x ^ 2)
  have h4 : 1 ≤ (Real.sqrt (1 + 2 * x) * exp (-x + x ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpos.le]
    exact h
  have h5 : 0 ≤ Real.sqrt (1 + 2 * x) * exp (-x + x ^ 2) := by positivity
  nlinarith

/-- **A lower tail for a nonnegative combination of squares of independent standard
Gaussians**: `Pr(Σ λ_i ξ_i² ≤ Σ λ_i − t) ≤ exp(−t²/(4B))` if `λ_i ≥ 0`, `Σ λ_i² ≤ B`. -/
theorem chiSqLower {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {B : ℝ} (hB : ∑ i, lam i ^ 2 ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    (stdGauss ι).real {ξ | ∑ i, lam i * ξ i ^ 2 ≤ ∑ i, lam i - t} ≤ exp (-t ^ 2 / (4 * B)) := by
  have hind : iIndepFun (fun (i : ι) (ξ : ι → ℝ) => lam i * ξ i ^ 2) (stdGauss ι) := by
    unfold stdGauss
    exact iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1)
      (X := fun i => fun x : ℝ => lam i * x ^ 2) (fun _ => by fun_prop)
  have hm : ∀ i : ι, Measurable (fun ξ : ι → ℝ => lam i * ξ i ^ 2) := fun i => by fun_prop
  have hval : ∀ (i : ι) (s : ℝ), 0 ≤ s →
      Integrable (fun ξ : ι → ℝ => exp (-s * (lam i * ξ i ^ 2))) (stdGauss ι) ∧
      ∫ ξ : ι → ℝ, exp (-s * (lam i * ξ i ^ 2)) ∂stdGauss ι =
        (Real.sqrt (1 + 2 * (s * lam i)))⁻¹ := by
    intro i s hs
    obtain ⟨hI, hE⟩ := gauss_laplace_sq (t := s * lam i) (mul_nonneg hs (hlam i))
    have e : (fun ξ : ι → ℝ => exp (-s * (lam i * ξ i ^ 2))) =
        fun ξ => (fun z : ℝ => exp (-(s * lam i) * z ^ 2)) (ξ i) := by
      funext ξ
      congr 1
      ring
    rw [e]
    unfold stdGauss
    refine ⟨integrable_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i) hI, ?_⟩
    rw [integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
      hI.aestronglyMeasurable, hE]
  have h := chernoffLower hind hm (a := lam) (b := fun i => 2 * lam i ^ 2)
    (fun i s hs => (hval i s hs).1)
    (fun i s hs => by
      unfold mgf
      rw [(hval i s hs).2]
      refine (inv_sqrt_le_exp (mul_nonneg hs (hlam i))).trans (le_of_eq ?_)
      congr 1
      ring)
    (B := 2 * B) (by rw [← Finset.mul_sum]; linarith) ht
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

/-- **A lower tail for a positive semidefinite Gaussian quadratic form**: for a symmetric
matrix `C` with `ξᵀCξ ≥ 0` for every `ξ`, and `Σ_{ij} C_{ij}² ≤ B`, `t ≥ 0`:
`Pr(ξᵀCξ ≤ tr C − t) ≤ exp(−t²/(4B))`, `ξ` a standard Gaussian vector. -/
theorem qformLower {ι : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℝ)
    (hC : C.transpose = C) (hpsd : ∀ ξ : ι → ℝ, 0 ≤ ξ ⬝ᵥ C *ᵥ ξ)
    {B : ℝ} (hB : ∑ i, ∑ j, C i j ^ 2 ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    (stdGauss ι).real {ξ | ξ ⬝ᵥ C *ᵥ ξ ≤ C.trace - t} ≤ exp (-t ^ 2 / (4 * B)) := by
  have hH : C.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hC
  obtain ⟨V, lam, hV, hform, htr, htr2, hposL⟩ := BstLean.Part109.diag_form C hH
  have e1 : ∀ ξ : ι → ℝ, ξ ⬝ᵥ C *ᵥ ξ = ∑ c, ∑ c', ξ c * ξ c' * C c c' := by
    intro ξ
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    ring
  have hl : ∀ i, 0 ≤ lam i := hposL fun ξ => by rw [← e1]; exact hpsd ξ
  set S : Set (ι → ℝ) := {ζ | ∑ i, lam i * ζ i ^ 2 ≤ ∑ i, lam i - t} with hS
  have mS : MeasurableSet S :=
    measurableSet_le (by fun_prop) measurable_const
  have hset : {ξ : ι → ℝ | ξ ⬝ᵥ C *ᵥ ξ ≤ C.trace - t} = {ξ | V.mulVec ξ ∈ S} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, hS]
    rw [e1, hform, htr]
    rfl
  rw [hset, BstLean.Part109.stdGauss_real_orth V hV mS]
  exact chiSqLower hl (by rw [htr2]; exact hB) ht

end BstLean.Part148

open BstLean.Part148 in
#print axioms chernoffLower
open BstLean.Part148 in
#print axioms expLowerTail_indep
open BstLean.Part148 in
#print axioms expLowerTail_pi
open BstLean.Part148 in
#print axioms gaussMat_rows_map
open BstLean.Part148 in
#print axioms expLowerTail_rows
open BstLean.Part148 in
#print axioms chiSqLower
open BstLean.Part148 in
#print axioms qformLower
