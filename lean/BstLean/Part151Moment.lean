import BstLean.Part151Gauss
import BstLean.Part151Tail

/-!
# Part 151, item 5 (first half): what the Gaussian last step gives when only the MEAN of the
conditional variance is known

Role: `delegations/statements/p151-spec.md`, item 5. This file is abstract (the setting of
`Part151Gauss`).

The existing Lean bounds of the `A` stage (Parts 149, 150) are second-moment bounds: they bound
`E[1_E·V]`, the mean of the conditional variance `V` of the error on an event `E`. Two ways to
use such a bound in the Gaussian last step:

1. Markov's inequality for `V` (the route named in the specification): an event `V ≤ v` with
   charge `E[1_E·V]/v`, then the Gaussian tail `2Φ̄(c/√v)`. **`markov_no_gain`**: with
   `q = E[1_E·V]/c²` (the bound of Chebyshev's inequality) and `a = c/√v`, the sum of the two
   charges is `q·a² + 2Φ̄(a) ≥ min(q, 6/25)`. So this route is never better than Chebyshev's
   inequality when Chebyshev's bound is below `6/25`.
2. The pointwise bound `2Φ̄(a) ≤ κ/a²` with `κ < 1`: **`two_PhiBar_le_kap`** (`κ = 2/5`; the
   best constant is `sup_a 2a²Φ̄(a) = 0.3311…`). It gives **`gaussStepMoment`**:
   `Pr(ω ∈ E, |lin| > c) ≤ κ·E[1_E·V]/c²`: Chebyshev's bound times `κ`. **`finalStepMoment`**:
   the union bound with this term.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open BstLean.Part131 (pdf_eq tail_one_gt)

/-! ## Markov's inequality gives no gain -/

/-- **Markov's inequality for the conditional variance, then the Gaussian tail, is not better
than Chebyshev's inequality.** `q ≥ 0` is Chebyshev's bound `E[1_E·V]/c²`; for the threshold
`v` of the variance put `a = c/√v`; the two charges are `q·a²` (Markov) and `2Φ̄(a)` (Gauss).
Their sum is at least `min(q, 6/25)` for every `a > 0`. -/
theorem markov_no_gain {q a : ℝ} (hq : 0 ≤ q) (ha : 0 < a) :
    min q (6 / 25) ≤ q * a ^ 2 + 2 * PhiBar a := by
  rcases le_total 1 a with h | h
  · have h1 : q ≤ q * a ^ 2 := by
      have : (1 : ℝ) ≤ a ^ 2 := by nlinarith
      nlinarith
    have := PhiBar_nonneg a
    exact (min_le_left _ _).trans (by linarith)
  · have h1 : PhiBar 1 ≤ PhiBar a := tail_anti h
    have h2 : (3 : ℝ) / 25 < PhiBar 1 := tail_one_gt
    have h3 : 0 ≤ q * a ^ 2 := by positivity
    exact (min_le_right _ _).trans (by linarith)

/-! ## The bound `2Φ̄(a) ≤ (2/5)/a²` -/

/-- `Φ̄(a) ≤ φ(a)·(a² + 2)/(a³ + 3a)` for `a > 0` (the second upper convergent of the continued
fraction of the Mills ratio). -/
theorem tail_le_conv2 {a : ℝ} (ha : 0 < a) :
    (gaussianReal 0 1).real (Ioi a) ≤
      gaussianPDFReal 0 1 a * ((a ^ 2 + 2) / (a ^ 3 + 3 * a)) := by
  refine tail_le_of (a := a) (K := 1 / a) (q := fun x => (x ^ 2 + 2) / (x ^ 3 + 3 * x))
    (q' := fun x => ((2 * x) * (x ^ 3 + 3 * x) - (x ^ 2 + 2) * (3 * x ^ 2 + 3)) /
      (x ^ 3 + 3 * x) ^ 2) ?_ ?_ ?_
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx
    have hden : x ^ 3 + 3 * x ≠ 0 := by positivity
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + 2) (2 * x) x := by
      have h := (hasDerivAt_pow 2 x).add_const (2 : ℝ)
      convert h using 1
      ring
    have h2 : HasDerivAt (fun x : ℝ => x ^ 3 + 3 * x) (3 * x ^ 2 + 3) x := by
      have h := (hasDerivAt_pow 3 x).add ((hasDerivAt_id' x).const_mul (3 : ℝ))
      convert h using 1
      ring
    exact h1.div h2 hden
  · intro x hx
    have hx0 : 0 < x := lt_trans ha hx
    have hden : 0 < x ^ 3 + 3 * x := by positivity
    have e : x * ((x ^ 2 + 2) / (x ^ 3 + 3 * x)) -
        ((2 * x) * (x ^ 3 + 3 * x) - (x ^ 2 + 2) * (3 * x ^ 2 + 3)) / (x ^ 3 + 3 * x) ^ 2 =
        1 + 6 / (x ^ 3 + 3 * x) ^ 2 := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ 6 / (x ^ 3 + 3 * x) ^ 2 := by positivity
    linarith
  · intro x hx
    have hx0 : 0 < x := lt_trans ha hx
    have hden : 0 < x ^ 3 + 3 * x := by positivity
    rw [abs_of_pos (by positivity)]
    calc (x ^ 2 + 2) / (x ^ 3 + 3 * x) ≤ 1 / x := by
          rw [div_le_div_iff₀ hden hx0]
          nlinarith [sq_nonneg x, hx0]
      _ ≤ 1 / a := one_div_le_one_div_of_le ha hx.le

/-- `s·e^{−s}·((s + 2)/(s + 3))² ≤ 1/4` for `s ≥ 0`. -/
lemma G_le_quarter {s : ℝ} (hs : 0 ≤ s) :
    s * Real.exp (-s) * ((s + 2) / (s + 3)) ^ 2 ≤ 1 / 4 := by
  have he1 : Real.exp (-1) ≤ 36788 / 100000 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    refine le_trans ?_ this.le
    norm_num
  have hr0 : 0 ≤ (s + 2) / (s + 3) := by positivity
  rcases le_total s (13 / 5) with h | h
  · -- `s·e^{−s} ≤ e^{−1}` and the ratio is at most `23/28`
    have h1 : s * Real.exp (-s) ≤ Real.exp (-1) := by
      have h0 := Real.add_one_le_exp (s - 1)
      have e : Real.exp (-1) = Real.exp (s - 1) * Real.exp (-s) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    have h2 : (s + 2) / (s + 3) ≤ 23 / 28 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h3 : ((s + 2) / (s + 3)) ^ 2 ≤ (23 / 28) ^ 2 := pow_le_pow_left₀ hr0 h2 2
    have h4 : 0 ≤ s * Real.exp (-s) := mul_nonneg hs (Real.exp_pos _).le
    calc s * Real.exp (-s) * ((s + 2) / (s + 3)) ^ 2
        ≤ (36788 / 100000) * (23 / 28) ^ 2 :=
          mul_le_mul (h1.trans he1) h3 (by positivity) (by norm_num)
      _ ≤ 1 / 4 := by norm_num
  · -- `e^s ≥ 4s`, and the ratio is at most `1`
    have h2 : (s + 2) / (s + 3) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have h3 : ((s + 2) / (s + 3)) ^ 2 ≤ 1 := pow_le_one₀ hr0 h2
    have hE : (13 : ℝ) ≤ Real.exp (13 / 5) := by
      have e : Real.exp (13 / 5) = Real.exp 1 * Real.exp 1 * Real.exp (3 / 5) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; norm_num
      have h1 := Real.exp_one_gt_d9
      have h4 := Real.quadratic_le_exp_of_nonneg (x := 3 / 5) (by norm_num)
      have h5 : (2.7182818283 : ℝ) * 2.7182818283 ≤ Real.exp 1 * Real.exp 1 :=
        mul_le_mul h1.le h1.le (by norm_num) (Real.exp_pos _).le
      rw [e]
      calc (13 : ℝ) ≤ 2.7182818283 * 2.7182818283 * (1 + 3 / 5 + (3 / 5) ^ 2 / 2) := by
            norm_num
        _ ≤ Real.exp 1 * Real.exp 1 * Real.exp (3 / 5) :=
            mul_le_mul h5 h4 (by norm_num) (by positivity)
    have h4 : 4 * s ≤ Real.exp s := by
      have e : Real.exp s = Real.exp (s - 13 / 5) * Real.exp (13 / 5) := by
        rw [← Real.exp_add]; congr 1; ring
      have h0 := Real.add_one_le_exp (s - 13 / 5)
      have h5 : 0 ≤ s - 13 / 5 + 1 := by linarith
      rw [e]
      calc 4 * s ≤ (s - 13 / 5 + 1) * 13 := by linarith
        _ ≤ Real.exp (s - 13 / 5) * Real.exp (13 / 5) :=
            mul_le_mul h0 hE (by norm_num) (Real.exp_pos _).le
    have h5 : s * Real.exp (-s) ≤ 1 / 4 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      linarith
    have h6 : 0 ≤ s * Real.exp (-s) := mul_nonneg hs (Real.exp_pos _).le
    calc s * Real.exp (-s) * ((s + 2) / (s + 3)) ^ 2 ≤ 1 / 4 * 1 :=
          mul_le_mul h5 h3 (by positivity) (by norm_num)
      _ = 1 / 4 := by ring

/-- **`2Φ̄(a) ≤ (2/5)/a²` for `a > 0`.** (Chebyshev's inequality gives `1/a²`; the best constant
is `0.3311…`.) -/
theorem two_PhiBar_le_kap {a : ℝ} (ha : 0 < a) : 2 * PhiBar a ≤ 2 / 5 / a ^ 2 := by
  have h1 := tail_le_conv2 ha
  have hpi := Real.pi_gt_d2
  have hsp : 0 < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  -- `y = φ(a)·a·(a² + 2)/(a² + 3)` and `y² ≤ 1/25`
  set y : ℝ := gaussianPDFReal 0 1 a * (a * ((a ^ 2 + 2) / (a ^ 2 + 3))) with hy
  have hy0 : 0 ≤ y := by
    rw [hy]
    exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (by positivity)
  have hG := G_le_quarter (s := a ^ 2) (by positivity)
  have hysq : y ^ 2 = 1 / (2 * Real.pi) *
      (a ^ 2 * Real.exp (-(a ^ 2)) * ((a ^ 2 + 2) / (a ^ 2 + 3)) ^ 2) := by
    rw [hy, pdf_eq]
    have e : Real.exp (-(a ^ 2)) = Real.exp (-(a ^ 2 / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [e]
    have hs2 : √(2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    field_simp
    rw [hs2]
  have hy2 : y ^ 2 ≤ (1 / 5) ^ 2 := by
    rw [hysq]
    calc 1 / (2 * Real.pi) * (a ^ 2 * Real.exp (-(a ^ 2)) * ((a ^ 2 + 2) / (a ^ 2 + 3)) ^ 2)
        ≤ 1 / (2 * Real.pi) * (1 / 4) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ ≤ (1 / 5) ^ 2 := by
          rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
          nlinarith
  have hy5 : y ≤ 1 / 5 := (abs_le_of_sq_le_sq' hy2 (by norm_num)).2
  have hrel : gaussianPDFReal 0 1 a * ((a ^ 2 + 2) / (a ^ 3 + 3 * a)) = y / a ^ 2 := by
    rw [hy]
    field_simp
  unfold PhiBar
  rw [hrel] at h1
  have h2 : y / a ^ 2 ≤ 1 / 5 / a ^ 2 := div_le_div_of_nonneg_right hy5 (by positivity)
  have e : (2 : ℝ) / 5 / a ^ 2 = 2 * (1 / 5 / a ^ 2) := by ring
  rw [e]
  linarith

/-! ## The Gaussian step in moment form -/

/-- A centred Gaussian variable with variance `V`: `Pr(|X| > c) ≤ κ·V/c²`, for every constant
`κ` with `2Φ̄(a) ≤ κ/a²` (for example `κ = 2/5`). -/
theorem gauss_abs_tail_moment {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2) {V c : ℝ}
    (hV0 : 0 ≤ V) (hc : 0 < c) :
    (gaussianReal 0 V.toNNReal).real {x | c < |x|} ≤ κ * V / c ^ 2 := by
  have hκ0 : 0 ≤ κ := by
    have h := hκ 1 one_pos
    have := PhiBar_nonneg 1
    simp only [one_pow, div_one] at h
    linarith
  rcases hV0.eq_or_lt with h0 | hVpos
  · rw [← h0]
    simp only [Real.toNNReal_zero, gaussianReal_zero_var, mul_zero, zero_div]
    have hms0 : MeasurableSet {x : ℝ | c < |x|} :=
      measurableSet_lt measurable_const measurable_id.abs
    rw [measureReal_def, Measure.dirac_apply' _ hms0]
    simp [not_lt.mpr hc.le]
  have h := gauss_abs_tail hV0 le_rfl hVpos hc
  have hsV : 0 < √V := Real.sqrt_pos.mpr hVpos
  have h2 := hκ (c / √V) (by positivity)
  have e : κ / (c / √V) ^ 2 = κ * V / c ^ 2 := by
    rw [div_pow, Real.sq_sqrt hV0]
    field_simp
  rw [e] at h2
  linarith

section step

variable {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]

/-- **The Gaussian step in moment form.** As `gaussStep`, with no bound of the conditional
variance `V` on `E`: `Pr(ω ∈ E and |lin| > c) ≤ (κ/c²)·E[1_E·V]`. With `κ = 1` this is
Chebyshev's inequality; `two_PhiBar_le_kap` allows `κ = 2/5`. -/
theorem gaussStepMoment {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure R) [IsProbabilityMeasure ν]
    {lin : Ω → R → ℝ} (hlin : Measurable fun p : Ω × R => lin p.1 p.2) {V : Ω → ℝ} {E : Set Ω}
    (hE : MeasurableSet E) (hV0 : ∀ ω ∈ E, 0 ≤ V ω)
    (hg : ∀ ω ∈ E, ν.map (lin ω) = gaussianReal 0 (V ω).toNNReal) {c : ℝ} (hc : 0 < c) {I : ℝ}
    (hI0 : 0 ≤ I) (hI : ∫⁻ ω in E, ENNReal.ofReal (V ω) ∂P ≤ ENNReal.ofReal I) :
    (P.prod ν).real {p | p.1 ∈ E ∧ c < |lin p.1 p.2|} ≤ κ * I / c ^ 2 := by
  have hκ0 : 0 ≤ κ := by
    have h := hκ 1 one_pos
    have := PhiBar_nonneg 1
    simp only [one_pow, div_one] at h
    linarith
  have hS : MeasurableSet {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|} :=
    (measurable_fst hE).inter (measurableSet_lt measurable_const hlin.abs)
  have hk0 : 0 ≤ κ / c ^ 2 := by positivity
  have hpt : ∀ ω, ν (Prod.mk ω ⁻¹' {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|}) ≤
      E.indicator (fun ω => ENNReal.ofReal (κ / c ^ 2) * ENNReal.ofReal (V ω)) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      have hlω : Measurable (lin ω) := hlin.comp (measurable_const.prodMk measurable_id)
      have hms : MeasurableSet {x : ℝ | c < |x|} :=
        measurableSet_lt measurable_const measurable_id.abs
      have e : Prod.mk ω ⁻¹' {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|} =
          lin ω ⁻¹' {x | c < |x|} := by
        ext w; simp [hω]
      rw [e, ← Measure.map_apply hlω hms, hg ω hω, ← ENNReal.ofReal_mul hk0]
      have h := gauss_abs_tail_moment hκ (hV0 ω hω) hc
      rw [measureReal_def] at h
      have e2 : κ / c ^ 2 * V ω = κ * V ω / c ^ 2 := by ring
      rw [e2]
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
        (by have := hV0 ω hω; positivity)).mpr h
    · rw [indicator_of_notMem hω]
      have e : Prod.mk ω ⁻¹' {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|} = ∅ := by
        ext w; simp [hω]
      rw [e]; simp
  have hle : (P.prod ν) {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|} ≤
      ENNReal.ofReal (κ / c ^ 2) * ENNReal.ofReal I := by
    rw [Measure.prod_apply hS]
    calc ∫⁻ ω, ν (Prod.mk ω ⁻¹' {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|}) ∂P
        ≤ ∫⁻ ω, E.indicator (fun ω => ENNReal.ofReal (κ / c ^ 2) * ENNReal.ofReal (V ω)) ω ∂P :=
          lintegral_mono hpt
      _ = ∫⁻ ω in E, ENNReal.ofReal (κ / c ^ 2) * ENNReal.ofReal (V ω) ∂P :=
          lintegral_indicator hE _
      _ = ENNReal.ofReal (κ / c ^ 2) * ∫⁻ ω in E, ENNReal.ofReal (V ω) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (κ / c ^ 2) * ENNReal.ofReal I := mul_le_mul' le_rfl hI
  rw [← ENNReal.ofReal_mul hk0] at hle
  rw [measureReal_def]
  have e2 : κ / c ^ 2 * I = κ * I / c ^ 2 := by ring
  rw [e2] at hle
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

end step

section final

variable {T Ω R : Type*} [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace R]

/-- **The union bound with the Gaussian step in moment form.** As `finalStep`, but the event `E`
carries no bound of the conditional variance; its mean on `E` is at most `I`. The first term is
restricted to `E` and to `sd ≥ d`:
`Pr(|g − B| > (ε_W + ε_A)·sd) ≤ Pr(E, sd ≥ d, |B′ − B| > ε_W·sd) + Pr(Eᶜ) + Pr(G, sd < d)
+ κ·I/(ε_A·d)²`. -/
theorem finalStepMoment {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (Q : Measure T) [IsProbabilityMeasure Q] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure R) [IsProbabilityMeasure ν] {rest : T → Ω}
    {row : T → R} (hrest : Measurable rest) (hrow : Measurable row)
    (hmap : Q.map (fun t => (rest t, row t)) = P.prod ν) {lin : Ω → R → ℝ}
    (hlin : Measurable fun p : Ω × R => lin p.1 p.2) {V : Ω → ℝ} {E : Set Ω}
    (hE : MeasurableSet E) (hV0 : ∀ ω ∈ E, 0 ≤ V ω)
    (hg : ∀ ω ∈ E, ν.map (lin ω) = gaussianReal 0 (V ω).toNNReal) {I : ℝ} (hI0 : 0 ≤ I)
    (hI : ∫⁻ ω in E, ENNReal.ofReal (V ω) ∂P ≤ ENNReal.ofReal I) (g B B' sd : T → ℝ)
    (hst : ∀ t, rest t ∈ E → g t - B' t = lin (rest t) (row t)) (G : Set T)
    (hEG : ∀ t, rest t ∈ E → t ∈ G) (εW : ℝ) {εA d : ℝ} (hεA : 0 < εA) (hd : 0 < d) :
    Q.real {t | (εW + εA) * sd t < |g t - B t|} ≤
      Q.real {t | rest t ∈ E ∧ d ≤ sd t ∧ εW * sd t < |B' t - B t|} + P.real Eᶜ +
        Q.real (G ∩ {t | sd t < d}) + κ * I / (εA * d) ^ 2 := by
  have hpair : Measurable fun t => (rest t, row t) := hrest.prodMk hrow
  have hincl : {t | (εW + εA) * sd t < |g t - B t|} ⊆
      (({t | rest t ∈ E ∧ d ≤ sd t ∧ εW * sd t < |B' t - B t|} ∪ rest ⁻¹' Eᶜ) ∪
        (G ∩ {t | sd t < d})) ∪
        (fun t => (rest t, row t)) ⁻¹' {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|} := by
    intro t ht
    simp only [mem_ofPred_eq] at ht
    by_cases h2 : rest t ∈ E
    swap
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : sd t < d
    · exact Or.inl (Or.inr ⟨hEG t h2, h3⟩)
    have h3' : d ≤ sd t := not_lt.mp h3
    by_cases h1 : εW * sd t < |B' t - B t|
    · exact Or.inl (Or.inl (Or.inl ⟨h2, h3', h1⟩))
    refine Or.inr ⟨h2, ?_⟩
    show εA * d < |lin (rest t) (row t)|
    rw [← hst t h2]
    have h1' : |B' t - B t| ≤ εW * sd t := not_lt.mp h1
    have htri : |g t - B t| ≤ |g t - B' t| + |B' t - B t| := by
      have := abs_add_le (g t - B' t) (B' t - B t)
      rwa [sub_add_sub_cancel] at this
    have : εA * d ≤ εA * sd t := mul_le_mul_of_nonneg_left h3' hεA.le
    nlinarith
  have hEc : Q.real (rest ⁻¹' Eᶜ) = P.real Eᶜ := by
    have h1 : P = Q.map rest := by
      have h := congrArg (Measure.map Prod.fst) hmap
      rw [Measure.map_map measurable_fst hpair] at h
      have e : (Prod.fst ∘ fun t => (rest t, row t)) = rest := rfl
      rw [e] at h
      rw [h]; simp
    rw [h1, map_measureReal_apply hrest hE.compl]
  have hS : MeasurableSet {p : Ω × R | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|} :=
    (measurable_fst hE).inter (measurableSet_lt measurable_const hlin.abs)
  have hG4 : Q.real ((fun t => (rest t, row t)) ⁻¹'
      {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|}) ≤ κ * I / (εA * d) ^ 2 := by
    rw [← map_measureReal_apply hpair hS, hmap]
    exact gaussStepMoment hκ P ν hlin hE hV0 hg (mul_pos hεA hd) hI0 hI
  calc Q.real {t | (εW + εA) * sd t < |g t - B t|}
      ≤ Q.real ((({t | rest t ∈ E ∧ d ≤ sd t ∧ εW * sd t < |B' t - B t|} ∪ rest ⁻¹' Eᶜ) ∪
        (G ∩ {t | sd t < d})) ∪
        (fun t => (rest t, row t)) ⁻¹' {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|}) :=
        measureReal_mono hincl
    _ ≤ Q.real {t | rest t ∈ E ∧ d ≤ sd t ∧ εW * sd t < |B' t - B t|} + Q.real (rest ⁻¹' Eᶜ) +
          Q.real (G ∩ {t | sd t < d}) +
        Q.real ((fun t => (rest t, row t)) ⁻¹' {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|}) := by
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        exact measureReal_union_le _ _
    _ ≤ _ := by rw [hEc]; linarith

end final

end BstLean.Part151
