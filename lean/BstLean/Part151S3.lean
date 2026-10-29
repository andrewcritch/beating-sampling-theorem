import BstLean.Part151S2

/-!
# Part 151: the inverse moments of `|c + τξ|²` (the last sentence of Lemma S)

Role: Lemma S of `proofs/option-n/theorem5-04-standin-structure.tex`, last statement
(`τ₀^{2p}·E|y|^{−2p} ≤ Π_{i=1}^p (n − 1 − 2i)^{−1}`), for `p = 1`.

Route (not the projection of the paper): `1/X = ∫_0^∞ e^{−tX} dt`, and the Laplace transform of
a non-central chi-square variable is at most the central one:
`E e^{−t(a + τZ)²} = (1 + 2tτ²)^{−1/2}·e^{−ta²/(1 + 2tτ²)} ≤ (1 + 2tτ²)^{−1/2}`. So
`E|c + τξ|^{−2} ≤ ∫_0^∞ (1 + 2tτ²)^{−n/2} dt = 1/(τ²(n − 2))`: the bound of the paper with
`n − 2` in the place of `n − 3`, for every `n ≥ 3` and every `c`.

* `laplace_one`: `E e^{−t(a + τZ)²} ≤ (1 + 2tτ²)^{−1/2}`.
* `laplace_vec`: `E e^{−t|c + τξ|²} ≤ (1 + 2tτ²)^{−n/2}`.
* **`inv_moment_lint`**, **`inv_moment`**: `τ²·E|c + τξ|^{−2} ≤ 1/(n − 2)` (`n ≥ 3`);
  `inv_moment_paper`: `≤ 1/(n − 3)` (`n ≥ 4`), the statement of the paper.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)

/-- `E e^{−t(a + τZ)²} ≤ (1 + 2tτ²)^{−1/2}` for a standard Gaussian variable `Z`, `t ≥ 0`. -/
theorem laplace_one {t : ℝ} (ht : 0 ≤ t) (a τ : ℝ) :
    ∫ x, Real.exp (-(t * (a + τ * x) ^ 2)) ∂gaussianReal 0 1 ≤ (√(1 + 2 * t * τ ^ 2))⁻¹ := by
  have hpi := Real.pi_pos
  set b : ℝ := t * τ ^ 2 + 1 / 2 with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  set s : ℝ := t * a * τ / b with hs
  set K : ℝ := (√(2 * Real.pi))⁻¹ * Real.exp (-(t * a ^ 2 / (2 * b))) with hK
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (-(t * (a + τ * x) ^ 2)) =
      K * Real.exp (-b * (x + s) ^ 2) := by
    intro x
    rw [smul_eq_mul, BstLean.Part131.pdf_eq, hK, mul_assoc, mul_assoc, ← Real.exp_add,
      ← Real.exp_add]
    congr 2
    rw [hs]
    field_simp
    rw [hb]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_add_right_eq_self (fun x => Real.exp (-b * x ^ 2)) s,
    integral_gaussian b]
  have h1 : Real.exp (-(t * a ^ 2 / (2 * b))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ t * a ^ 2 / (2 * b) := by positivity
    linarith
  have h2 : (√(2 * Real.pi))⁻¹ * √(Real.pi / b) = (√(1 + 2 * t * τ ^ 2))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [hb]
    field_simp
    ring
  rw [← h2, hK]
  have h3 : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  have h4 : 0 ≤ √(Real.pi / b) := Real.sqrt_nonneg _
  calc (√(2 * Real.pi))⁻¹ * Real.exp (-(t * a ^ 2 / (2 * b))) * √(Real.pi / b)
      ≤ (√(2 * Real.pi))⁻¹ * 1 * √(Real.pi / b) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) h4
    _ = _ := by ring

variable {n : ℕ}

/-- `E e^{−t|c + τξ|²} ≤ ((1 + 2tτ²)^{−1/2})ⁿ`, `ξ` a standard Gaussian vector of `ℝⁿ`. -/
theorem laplace_vec {t : ℝ} (ht : 0 ≤ t) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ ξ, Real.exp (-(t * normSq (c + τ • ξ))) ∂stdGauss (Fin n) ≤
      ((√(1 + 2 * t * τ ^ 2))⁻¹) ^ n := by
  have e : ∀ ξ : Fin n → ℝ, Real.exp (-(t * normSq (c + τ • ξ))) =
      ∏ i, Real.exp (-(t * (c i + τ * ξ i) ^ 2)) := by
    intro ξ
    rw [← Real.exp_sum]
    congr 1
    unfold normSq
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rfl
  simp_rw [e]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (-(t * (c i + τ * x) ^ 2)))]
  calc ∏ i, ∫ x, Real.exp (-(t * (c i + τ * x) ^ 2)) ∂gaussianReal 0 1
      ≤ ∏ _i : Fin n, (√(1 + 2 * t * τ ^ 2))⁻¹ :=
        Finset.prod_le_prod₀ (fun i _ => integral_nonneg fun x => (Real.exp_pos _).le)
          (fun i _ => laplace_one ht (c i) τ)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `∫_0^∞ e^{−tX} dt = 1/X` for `X > 0`. -/
lemma lint_exp_neg {X : ℝ} (hX : 0 < X) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * X))) = ENNReal.ofReal (1 / X) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(t * X))) (Ioi 0) := by
    have h := exp_neg_integrableOn_Ioi 0 hX
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun t => (Real.exp_pos _).le)]
  congr 1
  have h := integral_exp_mul_Ioi (a := -X) (by linarith) 0
  have e : (fun t : ℝ => Real.exp (-(t * X))) = fun t => Real.exp (-X * t) := by
    funext t; congr 1; ring
  rw [e, h]
  simp

/-- `∫_0^∞ ((1 + 2tτ²)^{−1/2})ⁿ dt = 1/(τ²(n − 2))` for `n ≥ 3`. -/
lemma lint_pow (hn : 3 ≤ n) {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (((√(1 + 2 * t * τ ^ 2))⁻¹) ^ n) =
      ENNReal.ofReal (1 / (τ ^ 2 * ((n : ℝ) - 2))) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set p : ℝ := 1 - (n : ℝ) / 2 with hp
  set g : ℝ → ℝ := fun t => -((1 + 2 * t * τ ^ 2) ^ p) / (τ ^ 2 * ((n : ℝ) - 2)) with hg
  set g' : ℝ → ℝ := fun t => ((√(1 + 2 * t * τ ^ 2))⁻¹) ^ n with hg'
  have hu : ∀ t : ℝ, 0 ≤ t → 0 < 1 + 2 * t * τ ^ 2 := fun t ht => by positivity
  have hpow : ∀ t : ℝ, 0 ≤ t → g' t = (1 + 2 * t * τ ^ 2) ^ (p - 1) := by
    intro t ht
    have h0 := hu t ht
    simp only [hg']
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h0.le, ← Real.rpow_natCast, ← Real.rpow_mul h0.le]
    congr 1
    rw [hp]; ring
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt g (g' t) t := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    have h0 := hu t ht0
    have h1 : HasDerivAt (fun t : ℝ => 1 + 2 * t * τ ^ 2) (2 * τ ^ 2) t := by
      have := (((hasDerivAt_id t).const_mul (2 : ℝ)).mul_const (τ ^ 2)).const_add 1
      simpa using this
    have h2 := (h1.rpow_const (p := p) (Or.inl h0.ne')).neg.div_const (τ ^ 2 * ((n : ℝ) - 2))
    rw [hpow t ht0]
    have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
    have hτ2 : τ ^ 2 ≠ 0 := by positivity
    have e : -(2 * τ ^ 2 * p * (1 + 2 * t * τ ^ 2) ^ (p - 1)) / (τ ^ 2 * ((n : ℝ) - 2)) =
        (1 + 2 * t * τ ^ 2) ^ (p - 1) := by
      rw [hp]
      field_simp
      ring
    rw [← e]
    exact h2
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g' t := fun t _ => by simp only [hg']; positivity
  have htend : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 1 + 2 * t * τ ^ 2) atTop atTop := by
      have h2 : Tendsto (fun t : ℝ => 2 * t * τ ^ 2) atTop atTop := by
        have := (tendsto_id (x := (atTop : Filter ℝ))).const_mul_atTop
          (by positivity : (0 : ℝ) < 2 * τ ^ 2)
        refine this.congr fun t => ?_
        simp only [id]; ring
      exact tendsto_atTop_add_const_left _ 1 h2
    have h3 : Tendsto (fun t : ℝ => (1 + 2 * t * τ ^ 2) ^ p) atTop (𝓝 0) := by
      have h4 := (tendsto_rpow_neg_atTop (y := (n : ℝ) / 2 - 1) (by linarith)).comp h1
      refine h4.congr fun t => ?_
      simp only [Function.comp]
      congr 1
      rw [hp]; ring
    have h5 := h3.neg.div_const (τ ^ 2 * ((n : ℝ) - 2))
    simpa [hg] using h5
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hpos t ht), hval]
  congr 1
  simp only [hg]
  have e1 : (1 + 2 * 0 * τ ^ 2 : ℝ) = 1 := by ring
  rw [e1, Real.one_rpow]
  ring

/-- **The inverse second moment, lower-integral form**: for `n ≥ 3`, `τ > 0`, every `c`:
`E 1/|c + τξ|² ≤ 1/(τ²(n − 2))`. -/
theorem inv_moment_lint (hn : 3 ≤ n) {τ : ℝ} (hτ : 0 < τ) (c : Fin n → ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (1 / normSq (c + τ • ξ)) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (1 / (τ ^ 2 * ((n : ℝ) - 2))) := by
  have hns : Continuous (fun ξ : Fin n → ℝ => normSq (c + τ • ξ)) := by
    unfold normSq; fun_prop
  have hm : Measurable (Function.uncurry fun (ξ : Fin n → ℝ) (t : ℝ) =>
      ENNReal.ofReal (Real.exp (-(t * normSq (c + τ • ξ))))) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    have h1 : Continuous (fun q : (Fin n → ℝ) × ℝ => normSq (c + τ • q.1)) :=
      hns.comp continuous_fst
    show Continuous fun q : (Fin n → ℝ) × ℝ => Real.exp (-(q.2 * normSq (c + τ • q.1)))
    exact Real.continuous_exp.comp (continuous_snd.mul h1).neg
  calc ∫⁻ ξ, ENNReal.ofReal (1 / normSq (c + τ • ξ)) ∂stdGauss (Fin n)
      ≤ ∫⁻ ξ, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * normSq (c + τ • ξ)))))
          ∂stdGauss (Fin n) := by
        refine lintegral_mono fun ξ => ?_
        rcases (normSq_nonneg (c + τ • ξ)).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · exact (lint_exp_neg hpos).ge
    _ = ∫⁻ t in Ioi (0 : ℝ), (∫⁻ ξ, ENNReal.ofReal (Real.exp (-(t * normSq (c + τ • ξ))))
          ∂stdGauss (Fin n)) := lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (((√(1 + 2 * t * τ ^ 2))⁻¹) ^ n) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
        have hi : Integrable (fun ξ : Fin n → ℝ => Real.exp (-(t * normSq (c + τ • ξ))))
            (stdGauss (Fin n)) := by
          refine Integrable.of_bound (by fun_prop : Continuous fun ξ : Fin n → ℝ =>
            Real.exp (-(t * normSq (c + τ • ξ)))).measurable.aestronglyMeasurable 1
            (Eventually.of_forall fun ξ => ?_)
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
          have := mul_nonneg ht0 (normSq_nonneg (c + τ • ξ))
          linarith
        rw [← ofReal_integral_eq_lintegral_ofReal hi
          (Eventually.of_forall fun ξ => (Real.exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal (laplace_vec ht0 c τ)
    _ = _ := lint_pow hn hτ

/-- **The inverse second moment** (Lemma S, last statement, `p = 1`, with `n − 2`): for `n ≥ 3`,
`τ > 0` and every `c`: `1/|c + τξ|²` is integrable and `τ²·E 1/|c + τξ|² ≤ 1/(n − 2)`. -/
theorem inv_moment (hn : 3 ≤ n) {τ : ℝ} (hτ : 0 < τ) (c : Fin n → ℝ) :
    Integrable (fun ξ : Fin n → ℝ => 1 / normSq (c + τ • ξ)) (stdGauss (Fin n)) ∧
      τ ^ 2 * ∫ ξ, 1 / normSq (c + τ • ξ) ∂stdGauss (Fin n) ≤ 1 / ((n : ℝ) - 2) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := inv_moment_lint hn hτ c
  have hmeas : Measurable (fun ξ : Fin n → ℝ => 1 / normSq (c + τ • ξ)) := by
    have hns : Continuous (fun ξ : Fin n → ℝ => normSq (c + τ • ξ)) := by
      unfold normSq; fun_prop
    exact measurable_const.div hns.measurable
  have h0 : ∀ ξ : Fin n → ℝ, 0 ≤ 1 / normSq (c + τ • ξ) := fun ξ =>
    div_nonneg zero_le_one (normSq_nonneg _)
  have hint : Integrable (fun ξ : Fin n → ℝ => 1 / normSq (c + τ • ξ)) (stdGauss (Fin n)) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall h0)
  rw [← h1] at hl
  have h2 : ∫ ξ, 1 / normSq (c + τ • ξ) ∂stdGauss (Fin n) ≤ 1 / (τ ^ 2 * ((n : ℝ) - 2)) :=
    (ENNReal.ofReal_le_ofReal_iff (by
      have : (0 : ℝ) < (n : ℝ) - 2 := by linarith
      positivity)).mp hl
  calc τ ^ 2 * ∫ ξ, 1 / normSq (c + τ • ξ) ∂stdGauss (Fin n)
      ≤ τ ^ 2 * (1 / (τ ^ 2 * ((n : ℝ) - 2))) := mul_le_mul_of_nonneg_left h2 (sq_nonneg τ)
    _ = 1 / ((n : ℝ) - 2) := by
        have : (n : ℝ) - 2 ≠ 0 := by linarith
        field_simp

/-- The statement of the paper: `τ²·E 1/|c + τξ|² ≤ 1/(n − 3)` for `n ≥ 4`. -/
theorem inv_moment_paper (hn : 4 ≤ n) {τ : ℝ} (hτ : 0 < τ) (c : Fin n → ℝ) :
    τ ^ 2 * ∫ ξ, 1 / normSq (c + τ • ξ) ∂stdGauss (Fin n) ≤ 1 / ((n : ℝ) - 3) := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  refine (inv_moment (by omega) hτ c).2.trans ?_
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

end BstLean.Part151
