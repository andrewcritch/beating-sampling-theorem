import BstLean.Part161Defs

/-!
# Part 161, items 1(a) and 1(d): the abstract root comparison lemmas (no network)

Role: `delegations/statements/p161-spec.md`. Do not use `sorry`, `native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:split` (the
replacement split) and the "Interface" paragraph (`|√P(C) − √P̃(C)| ≤ H(P, P̃)`).

`BstLean.Part138.hellSq ρ p q = ∫p + ∫q − 2∫√(pq)` is the squared Hellinger distance
`∫(√p − √q)² dρ` of the two densities `p`, `q` with respect to `ρ`.

* `sqrt_sub_sq_le_abs`: `(√x − √y)² ≤ |x − y|`.
* `root_dens_le`: `(√(∫_B p) − √(∫_B q))² ≤ hellSq ρ p q` for every measurable set `B`.
* `root_measure_le`: the same for the measures `P = p·ρ`, `Q = q·ρ`:
  `(√P(B) − √Q(B))² ≤ H²(P, Q)`.
* `hellSq_le_chi`: `H²(r·ρ, ρ) ≤ χ²(r·ρ ‖ ρ) = ∫(r − 1)² dρ`.
* `root_mix`: `(√(E X) − √(E Y))² ≤ E(√X − √Y)²` (the mixture inequality on one event).
* `root_mix_le`, `root_mix_abs`: the same with a pointwise bound.
* `removed`, `keptSet`, `goodMean`: the removed mass `β(a)`, the kept indices
  `{a ∈ I | β(a) ≤ η}`, the probability of the event under the normalized good-set mixture.
* **`root_split`**: the split of the root into removed mass, good-set mixture against one
  reference, displacement, bias, tails (Lemma `t7:p07:split`).
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open BstLean.Part138 (cs_sq hellSq)

variable {α : Type*} [MeasurableSpace α]

/-- `(√x − √y)² ≤ |x − y|` for `x, y ≥ 0`. -/
lemma sqrt_sub_sq_le_abs {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (√x - √y) ^ 2 ≤ |x - y| := by
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 := Real.sqrt_nonneg x
  have h4 := Real.sqrt_nonneg y
  have e : x - y = (√x - √y) * (√x + √y) := by nlinarith
  rw [e, abs_mul, abs_of_nonneg (add_nonneg h3 h4), sq, ← abs_mul_abs_self (√x - √y)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_le]
  constructor <;> linarith

/-- For roots in `[0, 1]`: `(√x − √y)² ≤ 1`. -/
lemma sqrt_sub_sq_le_one {x y : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (√x - √y) ^ 2 ≤ 1 := by
  refine (sqrt_sub_sq_le_abs hx hy).trans ?_
  rw [abs_le]
  constructor <;> linarith

/-- **The Hellinger root comparison, density form.** `p`, `q` are nonnegative integrable
densities with respect to `ρ`, `B` is a measurable set:
`(√(∫_B p dρ) − √(∫_B q dρ))² ≤ ∫(√p − √q)² dρ = hellSq ρ p q`. -/
theorem root_dens_le (ρ : Measure α) {p q : α → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (ip : Integrable p ρ) (iq : Integrable q ρ)
    {B : Set α} (hB : MeasurableSet B) :
    (√(∫ x, B.indicator 1 x * p x ∂ρ) - √(∫ x, B.indicator 1 x * q x ∂ρ)) ^ 2 ≤
      hellSq ρ p q := by
  set I : α → ℝ := B.indicator 1 with hI
  have mI : Measurable I := measurable_one.indicator hB
  have I01 : ∀ x, I x = 0 ∨ I x = 1 := by
    intro x
    by_cases h : x ∈ B
    · right; simp [hI, h]
    · left; simp [hI, h]
  have I0 : ∀ x, 0 ≤ I x := fun x => by rcases I01 x with h | h <;> simp [h]
  have I1 : ∀ x, I x ≤ 1 := fun x => by rcases I01 x with h | h <;> simp [h]
  have Isq : ∀ x, I x ^ 2 = I x := fun x => by rcases I01 x with h | h <;> simp [h]
  have sp : ∀ x, √(p x) ^ 2 = p x := fun x => Real.sq_sqrt (hp0 x)
  have sq' : ∀ x, √(q x) ^ 2 = q x := fun x => Real.sq_sqrt (hq0 x)
  have spq : ∀ x, √(p x * q x) = √(p x) * √(q x) := fun x => Real.sqrt_mul (hp0 x) _
  have iIp : Integrable (fun x => I x * p x) ρ := by
    refine ip.mono' (mI.mul hp).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (I0 x) (hp0 x))]
    exact mul_le_of_le_one_left (hp0 x) (I1 x)
  have iIq : Integrable (fun x => I x * q x) ρ := by
    refine iq.mono' (mI.mul hq).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (I0 x) (hq0 x))]
    exact mul_le_of_le_one_left (hq0 x) (I1 x)
  have ipq : Integrable (fun x => p x + q x) ρ := ip.add iq
  have isq : Integrable (fun x => √(p x * q x)) ρ := by
    refine ipq.mono' (hp.mul hq).sqrt.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), spq x]
    nlinarith [sq_nonneg (√(p x) - √(q x)), Real.sqrt_nonneg (p x), Real.sqrt_nonneg (q x),
      sp x, sq' x]
  have iIsq : Integrable (fun x => I x * √(p x * q x)) ρ := by
    refine isq.mono' (mI.mul (hp.mul hq).sqrt).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (I0 x) (Real.sqrt_nonneg _))]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (I1 x)
  set X := ∫ x, I x * p x ∂ρ with hX
  set Y := ∫ x, I x * q x ∂ρ with hY
  have hX0 : 0 ≤ X := integral_nonneg fun x => mul_nonneg (I0 x) (hp0 x)
  have hY0 : 0 ≤ Y := integral_nonneg fun x => mul_nonneg (I0 x) (hq0 x)
  -- Cauchy–Schwarz
  have e1 : (fun x => (I x * √(p x)) ^ 2) = fun x => I x * p x := by
    funext x; rw [mul_pow, Isq, sp]
  have e2 : (fun x => (I x * √(q x)) ^ 2) = fun x => I x * q x := by
    funext x; rw [mul_pow, Isq, sq']
  have e3 : (fun x => I x * √(p x) * (I x * √(q x))) = fun x => I x * √(p x * q x) := by
    funext x
    rw [spq x]
    calc I x * √(p x) * (I x * √(q x)) = I x ^ 2 * (√(p x) * √(q x)) := by ring
      _ = I x * (√(p x) * √(q x)) := by rw [Isq]
  have hcs := cs_sq ρ (f := fun x => I x * √(p x)) (g := fun x => I x * √(q x))
    (by rw [e1]; exact iIp) (by rw [e2]; exact iIq) (by rw [e3]; exact iIsq)
  rw [e1, e2, e3] at hcs
  have hZ0 : 0 ≤ ∫ x, I x * √(p x * q x) ∂ρ :=
    integral_nonneg fun x => mul_nonneg (I0 x) (Real.sqrt_nonneg _)
  have hZ : ∫ x, I x * √(p x * q x) ∂ρ ≤ √X * √Y := by
    rw [← Real.sqrt_mul hX0]
    exact Real.le_sqrt_of_sq_le hcs
  -- the pointwise bound
  have hpt : X + Y - 2 * ∫ x, I x * √(p x * q x) ∂ρ ≤ hellSq ρ p q := by
    have i3 : Integrable (fun x => I x * p x + I x * q x - 2 * (I x * √(p x * q x))) ρ :=
      (iIp.add iIq).sub (iIsq.const_mul 2)
    have i4 : Integrable (fun x => p x + q x - 2 * √(p x * q x)) ρ :=
      ipq.sub (isq.const_mul 2)
    have hm := integral_mono i3 i4 (fun x => by
      change I x * p x + I x * q x - 2 * (I x * √(p x * q x)) ≤ p x + q x - 2 * √(p x * q x)
      have h3 : I x * p x + I x * q x - 2 * (I x * √(p x * q x)) =
          I x * (√(p x) - √(q x)) ^ 2 := by
        rw [spq x]; linear_combination (-(I x)) * sp x + (-(I x)) * sq' x
      have h4 : p x + q x - 2 * √(p x * q x) = (√(p x) - √(q x)) ^ 2 := by
        rw [spq x]; linear_combination (-1 : ℝ) * sp x + (-1 : ℝ) * sq' x
      rw [h3, h4]
      exact mul_le_of_le_one_left (sq_nonneg _) (I1 x))
    have s1 : ∫ x, I x * p x + I x * q x - 2 * (I x * √(p x * q x)) ∂ρ =
        X + Y - 2 * ∫ x, I x * √(p x * q x) ∂ρ := by
      rw [integral_sub (f := fun x => I x * p x + I x * q x)
          (g := fun x => 2 * (I x * √(p x * q x))) (iIp.add iIq) (iIsq.const_mul 2),
        integral_add (f := fun x => I x * p x) (g := fun x => I x * q x) iIp iIq,
        integral_const_mul]
    have s2 : ∫ x, p x + q x - 2 * √(p x * q x) ∂ρ = hellSq ρ p q := by
      unfold hellSq
      rw [integral_sub (f := fun x => p x + q x) (g := fun x => 2 * √(p x * q x)) ipq
          (isq.const_mul 2), integral_add (f := p) (g := q) ip iq, integral_const_mul]
    rw [s1, s2] at hm
    exact hm
  have hsq : (√X - √Y) ^ 2 = X + Y - 2 * (√X * √Y) := by
    have e : (√X - √Y) ^ 2 = √X ^ 2 + √Y ^ 2 - 2 * (√X * √Y) := by ring
    rw [e, Real.sq_sqrt hX0, Real.sq_sqrt hY0]
  rw [hsq]
  linarith

/-- `(p·ρ)(B) = ∫_B p dρ` as a real number. -/
lemma withDensity_real (ρ : Measure α) {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (ip : Integrable p ρ) {B : Set α} (hB : MeasurableSet B) :
    (ρ.withDensity (fun x => ENNReal.ofReal (p x))).real B = ∫ x, B.indicator 1 x * p x ∂ρ := by
  have e : (fun x => B.indicator (1 : α → ℝ) x * p x) = B.indicator p := by
    funext x
    by_cases h : x ∈ B <;> simp [h]
  rw [e, integral_indicator hB, measureReal_def, withDensity_apply _ hB,
    ← ofReal_integral_eq_lintegral_ofReal ip.integrableOn
      (Filter.Eventually.of_forall fun x => hp0 x),
    ENNReal.toReal_ofReal (integral_nonneg fun x => hp0 x)]

/-- **The Hellinger root comparison (item 1(a)).** `P = p·ρ`, `Q = q·ρ` (for example two
probability measures with densities `p`, `q`), `B` a measurable set:
`(√P(B) − √Q(B))² ≤ H²(P, Q)`, `H² = ∫(√p − √q)² dρ`. -/
theorem root_measure_le (ρ : Measure α) {p q : α → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (ip : Integrable p ρ) (iq : Integrable q ρ)
    {B : Set α} (hB : MeasurableSet B) :
    (√((ρ.withDensity (fun x => ENNReal.ofReal (p x))).real B) -
      √((ρ.withDensity (fun x => ENNReal.ofReal (q x))).real B)) ^ 2 ≤ hellSq ρ p q := by
  rw [withDensity_real ρ hp0 ip hB, withDensity_real ρ hq0 iq hB]
  exact root_dens_le ρ hp hq hp0 hq0 ip iq hB

/-- The absolute form: `|√P(B) − √Q(B)| ≤ H(P, Q)`. -/
theorem root_measure_abs (ρ : Measure α) {p q : α → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (ip : Integrable p ρ) (iq : Integrable q ρ)
    {B : Set α} (hB : MeasurableSet B) :
    |√((ρ.withDensity (fun x => ENNReal.ofReal (p x))).real B) -
      √((ρ.withDensity (fun x => ENNReal.ofReal (q x))).real B)| ≤ √(hellSq ρ p q) :=
  Real.abs_le_sqrt (root_measure_le ρ hp hq hp0 hq0 ip iq hB)

/-- **`H² ≤ χ²`.** `ρ` a probability measure, `r ≥ 0` a probability density with respect to `ρ`
with `(r − 1)²` integrable: `H²(r·ρ, ρ) = ∫(√r − 1)² dρ ≤ ∫(r − 1)² dρ = χ²(r·ρ ‖ ρ)`. -/
theorem hellSq_le_chi (ρ : Measure α) [IsProbabilityMeasure ρ] {r : α → ℝ} (hr : Measurable r)
    (hr0 : ∀ x, 0 ≤ r x) (ir : Integrable r ρ)
    (i2 : Integrable (fun x => (r x - 1) ^ 2) ρ) :
    hellSq ρ r (fun _ => 1) ≤ ∫ x, (r x - 1) ^ 2 ∂ρ := by
  have isq : Integrable (fun x => √(r x * 1)) ρ := by
    refine (ir.add (integrable_const (1 : ℝ))).mono' (hr.mul measurable_const).sqrt.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
    change √(r x) ≤ r x + 1
    nlinarith [Real.sq_sqrt (hr0 x), Real.sqrt_nonneg (r x), sq_nonneg (√(r x) - 1)]
  have e : hellSq ρ r (fun _ => 1) = ∫ x, r x + 1 - 2 * √(r x * 1) ∂ρ := by
    unfold hellSq
    rw [integral_sub (f := fun x => r x + 1) (g := fun x => 2 * √(r x * 1))
        (ir.add (integrable_const 1)) (isq.const_mul 2),
      integral_add (f := r) (g := fun _ => (1 : ℝ)) ir (integrable_const 1), integral_const_mul]
  rw [e]
  refine integral_mono ((ir.add (integrable_const 1)).sub (isq.const_mul 2)) i2 (fun x => ?_)
  change r x + 1 - 2 * √(r x * 1) ≤ (r x - 1) ^ 2
  rw [mul_one]
  have h1 := Real.sq_sqrt (hr0 x)
  have h3 := Real.sqrt_nonneg (r x)
  have e1 : r x + 1 - 2 * √(r x) = (√(r x) - 1) ^ 2 := by nlinarith
  have e2 : (r x - 1) ^ 2 = (√(r x) - 1) ^ 2 * (√(r x) + 1) ^ 2 := by
    have : r x - 1 = (√(r x) - 1) * (√(r x) + 1) := by nlinarith
    rw [this]; ring
  rw [e1, e2]
  have h5 : 1 ≤ (√(r x) + 1) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (√(r x) - 1)]

/-! ## Mixtures on one event -/

/-- **The mixture inequality on one event.** `μ` a probability measure, `X`, `Y` measurable with
values in `[0, 1]` (the probabilities of one event under two families of distributions):
`(√(E X) − √(E Y))² ≤ E(√X − √Y)²`. -/
theorem root_mix (μ : Measure α) [IsProbabilityMeasure μ] {X Y : α → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (hX0 : ∀ a, 0 ≤ X a) (hX1 : ∀ a, X a ≤ 1) (hY0 : ∀ a, 0 ≤ Y a)
    (hY1 : ∀ a, Y a ≤ 1) :
    (√(∫ a, X a ∂μ) - √(∫ a, Y a ∂μ)) ^ 2 ≤ ∫ a, (√(X a) - √(Y a)) ^ 2 ∂μ := by
  have bd : ∀ {Z : α → ℝ}, Measurable Z → (∀ a, 0 ≤ Z a) → (∀ a, Z a ≤ 1) → Integrable Z μ :=
    fun {Z} hZ h0 h1 => Integrable.of_bound hZ.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 a)]; exact h1 a)
  have s1 : ∀ {z : ℝ}, 0 ≤ z → z ≤ 1 → √z ≤ 1 := fun {z} _ h1 => by
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at this
  have iX := bd hX hX0 hX1
  have iY := bd hY hY0 hY1
  have iP : Integrable (fun a => √(X a) * √(Y a)) μ :=
    bd (hX.sqrt.mul hY.sqrt) (fun a => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (fun a => by
        nlinarith [s1 (hX0 a) (hX1 a), s1 (hY0 a) (hY1 a), Real.sqrt_nonneg (X a),
          Real.sqrt_nonneg (Y a)])
  have eX : (fun a => √(X a) ^ 2) = X := funext fun a => Real.sq_sqrt (hX0 a)
  have eY : (fun a => √(Y a) ^ 2) = Y := funext fun a => Real.sq_sqrt (hY0 a)
  have hcs := cs_sq μ (f := fun a => √(X a)) (g := fun a => √(Y a))
    (by rw [eX]; exact iX) (by rw [eY]; exact iY) iP
  rw [eX, eY] at hcs
  have hEX0 : 0 ≤ ∫ a, X a ∂μ := integral_nonneg hX0
  have hEY0 : 0 ≤ ∫ a, Y a ∂μ := integral_nonneg hY0
  have hP : ∫ a, √(X a) * √(Y a) ∂μ ≤ √(∫ a, X a ∂μ) * √(∫ a, Y a ∂μ) := by
    rw [← Real.sqrt_mul hEX0]
    exact Real.le_sqrt_of_sq_le hcs
  have e : (fun a => (√(X a) - √(Y a)) ^ 2) = fun a => X a + Y a - 2 * (√(X a) * √(Y a)) := by
    funext a
    have e' : (√(X a) - √(Y a)) ^ 2 = √(X a) ^ 2 + √(Y a) ^ 2 - 2 * (√(X a) * √(Y a)) := by ring
    rw [e', Real.sq_sqrt (hX0 a), Real.sq_sqrt (hY0 a)]
  rw [e, integral_sub (f := fun a => X a + Y a) (g := fun a => 2 * (√(X a) * √(Y a)))
      (iX.add iY) (iP.const_mul 2), integral_add (f := X) (g := Y) iX iY, integral_const_mul]
  have hsq : (√(∫ a, X a ∂μ) - √(∫ a, Y a ∂μ)) ^ 2 =
      ∫ a, X a ∂μ + ∫ a, Y a ∂μ - 2 * (√(∫ a, X a ∂μ) * √(∫ a, Y a ∂μ)) := by
    have e' : (√(∫ a, X a ∂μ) - √(∫ a, Y a ∂μ)) ^ 2 =
        √(∫ a, X a ∂μ) ^ 2 + √(∫ a, Y a ∂μ) ^ 2 - 2 * (√(∫ a, X a ∂μ) * √(∫ a, Y a ∂μ)) := by
      ring
    rw [e', Real.sq_sqrt hEX0, Real.sq_sqrt hEY0]
  rw [hsq]
  linarith

/-- The mixture inequality with a pointwise bound `K`. -/
theorem root_mix_le (μ : Measure α) [IsProbabilityMeasure μ] {X Y K : α → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (hX0 : ∀ a, 0 ≤ X a) (hX1 : ∀ a, X a ≤ 1) (hY0 : ∀ a, 0 ≤ Y a)
    (hY1 : ∀ a, Y a ≤ 1) (iK : Integrable K μ) (h : ∀ a, (√(X a) - √(Y a)) ^ 2 ≤ K a) :
    (√(∫ a, X a ∂μ) - √(∫ a, Y a ∂μ)) ^ 2 ≤ ∫ a, K a ∂μ := by
  refine (root_mix μ hX hY hX0 hX1 hY0 hY1).trans (integral_mono ?_ iK h)
  refine Integrable.of_bound ((hX.sqrt.sub hY.sqrt).pow_const 2).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sqrt_sub_sq_le_one (hX0 a) (hX1 a) (hY0 a) (hY1 a)

/-- The absolute form: `|√(E X) − √(E Y)| ≤ √(E K)`. -/
theorem root_mix_abs (μ : Measure α) [IsProbabilityMeasure μ] {X Y K : α → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (hX0 : ∀ a, 0 ≤ X a) (hX1 : ∀ a, X a ≤ 1) (hY0 : ∀ a, 0 ≤ Y a)
    (hY1 : ∀ a, Y a ≤ 1) (iK : Integrable K μ) (h : ∀ a, (√(X a) - √(Y a)) ^ 2 ≤ K a) :
    |√(∫ a, X a ∂μ) - √(∫ a, Y a ∂μ)| ≤ √(∫ a, K a ∂μ) :=
  Real.abs_le_sqrt (root_mix_le μ hX hY hX0 hX1 hY0 hY1 iK h)

end BstLean.Part161

open BstLean.Part161 in
#print axioms root_measure_le
open BstLean.Part161 in
#print axioms hellSq_le_chi
open BstLean.Part161 in
#print axioms root_mix
