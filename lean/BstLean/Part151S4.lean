import BstLean.Part151S3

/-!
# Part 151: the inverse fourth moment of `|c + τξ|` (Lemma S, last statement, `p = 2`)

Route: `1/X² = ∫_0^∞∫_0^∞ e^{−(s+t)X} ds dt`, the Laplace bound `laplace_vec`, and
`∫_0^∞ (1 + 2(s + t)τ²)^{−n/2} dt = (1 + 2sτ²)^{−(n−2)/2}/(τ²(n − 2))`.

* `lint_pow_shift`: the last integral.
* **`inv_moment4_lint`**, **`inv_moment4`**: `τ⁴·E|c + τξ|^{−4} ≤ 1/((n − 2)(n − 4))` for
  `n ≥ 5`; `inv_moment4_paper`: `≤ 1/((n − 3)(n − 5))` for `n ≥ 6` (the statement of the paper).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)

variable {n : ℕ}

/-- `∫_0^∞ ((1 + 2(s + t)τ²)^{−1/2})ⁿ dt = ((1 + 2sτ²)^{−1/2})^{n−2}/(τ²(n − 2))`, `n ≥ 3`,
`s ≥ 0`. -/
lemma lint_pow_shift (hn : 3 ≤ n) {τ : ℝ} (hτ : 0 < τ) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (((√(1 + 2 * (s + t) * τ ^ 2))⁻¹) ^ n) =
      ENNReal.ofReal (((√(1 + 2 * s * τ ^ 2))⁻¹) ^ (n - 2) / (τ ^ 2 * ((n : ℝ) - 2))) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set p : ℝ := 1 - (n : ℝ) / 2 with hp
  set g : ℝ → ℝ := fun t => -((1 + 2 * (s + t) * τ ^ 2) ^ p) / (τ ^ 2 * ((n : ℝ) - 2)) with hg
  set g' : ℝ → ℝ := fun t => ((√(1 + 2 * (s + t) * τ ^ 2))⁻¹) ^ n with hg'
  have hu : ∀ t : ℝ, 0 ≤ t → 0 < 1 + 2 * (s + t) * τ ^ 2 := fun t ht => by positivity
  have hpow : ∀ t : ℝ, 0 ≤ t → g' t = (1 + 2 * (s + t) * τ ^ 2) ^ (p - 1) := by
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
    have h1 : HasDerivAt (fun t : ℝ => 1 + 2 * (s + t) * τ ^ 2) (2 * τ ^ 2) t := by
      have := ((((hasDerivAt_id t).const_add s).const_mul (2 : ℝ)).mul_const (τ ^ 2)).const_add 1
      simpa using this
    have h2 := (h1.rpow_const (p := p) (Or.inl h0.ne')).neg.div_const (τ ^ 2 * ((n : ℝ) - 2))
    rw [hpow t ht0]
    have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
    have hτ2 : τ ^ 2 ≠ 0 := by positivity
    have e : -(2 * τ ^ 2 * p * (1 + 2 * (s + t) * τ ^ 2) ^ (p - 1)) / (τ ^ 2 * ((n : ℝ) - 2)) =
        (1 + 2 * (s + t) * τ ^ 2) ^ (p - 1) := by
      rw [hp]
      field_simp
      ring
    rw [← e]
    exact h2
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g' t := fun t _ => by simp only [hg']; positivity
  have htend : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 1 + 2 * (s + t) * τ ^ 2) atTop atTop := by
      have h2 : Tendsto (fun t : ℝ => 2 * τ ^ 2 * t) atTop atTop :=
        (tendsto_id (x := (atTop : Filter ℝ))).const_mul_atTop
          (by positivity : (0 : ℝ) < 2 * τ ^ 2)
      have h3 := tendsto_atTop_add_const_left _ (1 + 2 * s * τ ^ 2) h2
      refine h3.congr fun t => ?_
      ring
    have h3 : Tendsto (fun t : ℝ => (1 + 2 * (s + t) * τ ^ 2) ^ p) atTop (𝓝 0) := by
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
  have h0 : 0 < 1 + 2 * s * τ ^ 2 := by positivity
  have e1 : (1 + 2 * (s + 0) * τ ^ 2 : ℝ) = 1 + 2 * s * τ ^ 2 := by ring
  have e2 : (1 + 2 * s * τ ^ 2) ^ p = ((√(1 + 2 * s * τ ^ 2))⁻¹) ^ (n - 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h0.le]
    rw [← Real.rpow_natCast ((1 + 2 * s * τ ^ 2) ^ (-(1 / 2 : ℝ))) (n - 2),
      ← Real.rpow_mul h0.le]
    congr 1
    rw [Nat.cast_sub (by omega), hp]
    push_cast
    ring
  rw [e1, e2]
  ring

/-- `1/X² = ∫_0^∞∫_0^∞ e^{−(s+t)X} dt ds` for `X > 0`. -/
lemma lint_exp_neg2 {X : ℝ} (hX : 0 < X) :
    ∫⁻ s in Ioi (0 : ℝ), (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-((s + t) * X)))) =
      ENNReal.ofReal (1 / X ^ 2) := by
  have e : ∀ s t : ℝ, ENNReal.ofReal (Real.exp (-((s + t) * X))) =
      ENNReal.ofReal (Real.exp (-(s * X))) * ENNReal.ofReal (Real.exp (-(t * X))) := by
    intro s t
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  simp_rw [e]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lint_exp_neg hX]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lint_exp_neg hX,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- **The inverse fourth moment, lower-integral form**: for `n ≥ 5`, `τ > 0`, every `c`:
`E 1/|c + τξ|⁴ ≤ 1/(τ⁴(n − 2)(n − 4))`. -/
theorem inv_moment4_lint (hn : 5 ≤ n) {τ : ℝ} (hτ : 0 < τ) (c : Fin n → ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (1 / normSq (c + τ • ξ) ^ 2) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (1 / (τ ^ 4 * (((n : ℝ) - 2) * ((n : ℝ) - 4)))) := by
  have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hns : Continuous (fun ξ : Fin n → ℝ => normSq (c + τ • ξ)) := by
    unfold normSq; fun_prop
  -- the integrand, jointly measurable in `(ξ, s, t)`
  set F : (Fin n → ℝ) → ℝ → ℝ → ℝ≥0∞ := fun ξ s t =>
    ENNReal.ofReal (Real.exp (-((s + t) * normSq (c + τ • ξ)))) with hF
  have hF3 : Measurable (fun q : ((Fin n → ℝ) × ℝ) × ℝ => F q.1.1 q.1.2 q.2) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    have h1 : Continuous (fun q : ((Fin n → ℝ) × ℝ) × ℝ => normSq (c + τ • q.1.1)) :=
      hns.comp (continuous_fst.comp continuous_fst)
    exact Real.continuous_exp.comp
      ((((continuous_snd.comp continuous_fst).add continuous_snd).mul h1).neg)
  have hinner : Measurable (fun q : (Fin n → ℝ) × ℝ => ∫⁻ t in Ioi (0 : ℝ), F q.1 q.2 t) :=
    hF3.lintegral_prod_right'
  have hF2 : ∀ s : ℝ, Measurable (Function.uncurry fun (ξ : Fin n → ℝ) (t : ℝ) => F ξ s t) := by
    intro s
    have h := hF3.comp (f := fun q : (Fin n → ℝ) × ℝ => ((q.1, s), q.2)) (by fun_prop)
    exact h
  have hq : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∫⁻ ξ, F ξ s t ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (((√(1 + 2 * (s + t) * τ ^ 2))⁻¹) ^ n) := by
    intro s t hs ht
    have hst : 0 ≤ s + t := add_nonneg hs ht
    have hi : Integrable (fun ξ : Fin n → ℝ => Real.exp (-((s + t) * normSq (c + τ • ξ))))
        (stdGauss (Fin n)) := by
      refine Integrable.of_bound (by fun_prop : Continuous fun ξ : Fin n → ℝ =>
        Real.exp (-((s + t) * normSq (c + τ • ξ)))).measurable.aestronglyMeasurable 1
        (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have := mul_nonneg hst (normSq_nonneg (c + τ • ξ))
      linarith
    simp only [hF]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun ξ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (laplace_vec hst c τ)
  calc ∫⁻ ξ, ENNReal.ofReal (1 / normSq (c + τ • ξ) ^ 2) ∂stdGauss (Fin n)
      ≤ ∫⁻ ξ, (∫⁻ s in Ioi (0 : ℝ), (∫⁻ t in Ioi (0 : ℝ), F ξ s t)) ∂stdGauss (Fin n) := by
        refine lintegral_mono fun ξ => ?_
        rcases (normSq_nonneg (c + τ • ξ)).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · exact (lint_exp_neg2 hpos).ge
    _ = ∫⁻ s in Ioi (0 : ℝ), (∫⁻ ξ, (∫⁻ t in Ioi (0 : ℝ), F ξ s t) ∂stdGauss (Fin n)) :=
        lintegral_lintegral_swap hinner.aemeasurable
    _ = ∫⁻ s in Ioi (0 : ℝ), (∫⁻ t in Ioi (0 : ℝ), (∫⁻ ξ, F ξ s t ∂stdGauss (Fin n))) := by
        refine lintegral_congr fun s => ?_
        exact lintegral_lintegral_swap (hF2 s).aemeasurable
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), (∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (((√(1 + 2 * (s + t) * τ ^ 2))⁻¹) ^ n)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
        exact setLIntegral_mono' measurableSet_Ioi fun t ht => hq s t (le_of_lt hs) (le_of_lt ht)
    _ = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
          (((√(1 + 2 * s * τ ^ 2))⁻¹) ^ (n - 2) / (τ ^ 2 * ((n : ℝ) - 2))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        exact lint_pow_shift (by omega) hτ (le_of_lt hs)
    _ = ENNReal.ofReal (1 / (τ ^ 2 * ((n : ℝ) - 2))) *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (((√(1 + 2 * s * τ ^ 2))⁻¹) ^ (n - 2)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun s => ?_
        rw [← ENNReal.ofReal_mul (by
          have : (0 : ℝ) < (n : ℝ) - 2 := by linarith
          positivity)]
        congr 1
        ring
    _ = ENNReal.ofReal (1 / (τ ^ 2 * ((n : ℝ) - 2))) *
          ENNReal.ofReal (1 / (τ ^ 2 * (((n - 2 : ℕ) : ℝ) - 2))) := by
        rw [lint_pow (by omega : 3 ≤ n - 2) hτ]
    _ = _ := by
        have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
        have h4 : (0 : ℝ) < (n : ℝ) - 4 := by linarith
        rw [← ENNReal.ofReal_mul (by positivity), Nat.cast_sub (by omega)]
        congr 1
        push_cast
        have h4' : (n : ℝ) - 2 - 2 = n - 4 := by ring
        rw [h4', one_div_mul_one_div]
        congr 1
        ring

/-- **The inverse fourth moment** (Lemma S, last statement, `p = 2`): for `n ≥ 5`, `τ > 0` and
every `c`: `1/|c + τξ|⁴` is integrable and `τ⁴·E 1/|c + τξ|⁴ ≤ 1/((n − 2)(n − 4))`. -/
theorem inv_moment4 (hn : 5 ≤ n) {τ : ℝ} (hτ : 0 < τ) (c : Fin n → ℝ) :
    Integrable (fun ξ : Fin n → ℝ => 1 / normSq (c + τ • ξ) ^ 2) (stdGauss (Fin n)) ∧
      τ ^ 4 * ∫ ξ, 1 / normSq (c + τ • ξ) ^ 2 ∂stdGauss (Fin n) ≤
        1 / (((n : ℝ) - 2) * ((n : ℝ) - 4)) := by
  have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have h4 : (0 : ℝ) < (n : ℝ) - 4 := by linarith
  have hl := inv_moment4_lint hn hτ c
  have hmeas : Measurable (fun ξ : Fin n → ℝ => 1 / normSq (c + τ • ξ) ^ 2) := by
    have hns : Continuous (fun ξ : Fin n → ℝ => normSq (c + τ • ξ)) := by
      unfold normSq; fun_prop
    exact measurable_const.div (hns.measurable.pow_const 2)
  have h0 : ∀ ξ : Fin n → ℝ, 0 ≤ 1 / normSq (c + τ • ξ) ^ 2 := fun ξ => by positivity
  have hint : Integrable (fun ξ : Fin n → ℝ => 1 / normSq (c + τ • ξ) ^ 2)
      (stdGauss (Fin n)) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall h0)
  rw [← h1] at hl
  have h3 : ∫ ξ, 1 / normSq (c + τ • ξ) ^ 2 ∂stdGauss (Fin n) ≤
      1 / (τ ^ 4 * (((n : ℝ) - 2) * ((n : ℝ) - 4))) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hl
  calc τ ^ 4 * ∫ ξ, 1 / normSq (c + τ • ξ) ^ 2 ∂stdGauss (Fin n)
      ≤ τ ^ 4 * (1 / (τ ^ 4 * (((n : ℝ) - 2) * ((n : ℝ) - 4)))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 1 / (((n : ℝ) - 2) * ((n : ℝ) - 4)) := by
        field_simp

/-- The statement of the paper: `τ⁴·E 1/|c + τξ|⁴ ≤ 1/((n − 3)(n − 5))` for `n ≥ 6`. -/
theorem inv_moment4_paper (hn : 6 ≤ n) {τ : ℝ} (hτ : 0 < τ) (c : Fin n → ℝ) :
    τ ^ 4 * ∫ ξ, 1 / normSq (c + τ • ξ) ^ 2 ∂stdGauss (Fin n) ≤
      1 / (((n : ℝ) - 3) * ((n : ℝ) - 5)) := by
  have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  refine (inv_moment4 (by omega) hτ c).2.trans ?_
  refine one_div_le_one_div_of_le (by nlinarith) (by nlinarith)

end BstLean.Part151
