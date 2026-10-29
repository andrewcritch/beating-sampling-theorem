import BstLean.Part136Joint

/-!
# Part 138, item 1: the Hellinger inequality for the difference of two means

Role: `delegations/statements/p138-spec.md`. Paper sources: `onW5-opus-prover.md` §4.5
(Lemma D3) and `onW6c-cx.md` §6: `|E_P h − E_Q h|² ≤ 2H²(E_P h² + E_Q h²)`,
`H² = ∫(√p − √q)²`.

`ρ` is a reference measure, `p`, `q` are densities with respect to `ρ` (nonnegative, measurable,
integrable). `hellSq ρ p q = ∫p + ∫q − 2∫√(pq)` is the squared Hellinger distance `∫(√p − √q)²`
(for two probability densities: `2 − 2·(affinity)`).

* `cs_sq`: Cauchy–Schwarz for integrals of real functions (no boundedness).
* `hell_core`: the inequality with the square roots `a = √p`, `b = √q` as the data.
* `hell_fn`: the inequality with the densities as weights.
* **`hellMean138`**: the inequality for the measures `P = p·ρ`, `Q = q·ρ`.
* `hellMean138_bdd`: for `|h| ≤ B` and probability measures: `(E_P h − E_Q h)² ≤ 4B²·H²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part138

open MeasureTheory ProbabilityTheory Real

variable {α : Type*} [MeasurableSpace α]

/-- **Cauchy–Schwarz** for integrals: `(∫fg)² ≤ ∫f²·∫g²`. -/
lemma cs_sq (ρ : Measure α) {f g : α → ℝ} (hf : Integrable (fun x => f x ^ 2) ρ)
    (hg : Integrable (fun x => g x ^ 2) ρ) (hfg : Integrable (fun x => f x * g x) ρ) :
    (∫ x, f x * g x ∂ρ) ^ 2 ≤ (∫ x, f x ^ 2 ∂ρ) * ∫ x, g x ^ 2 ∂ρ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, g x ^ 2 ∂ρ) * (t * t) + (2 * ∫ x, f x * g x ∂ρ) * t +
      ∫ x, f x ^ 2 ∂ρ := by
    intro t
    have h0 : 0 ≤ ∫ x, (f x + t * g x) ^ 2 ∂ρ := integral_nonneg fun x => sq_nonneg _
    have h1 : (fun x => (f x + t * g x) ^ 2) =
        fun x => (f x ^ 2 + (2 * t) * (f x * g x)) + (t * t) * g x ^ 2 := by
      funext x; ring
    have i1 : Integrable (fun x => (2 * t) * (f x * g x)) ρ := hfg.const_mul _
    have i2 : Integrable (fun x => f x ^ 2 + (2 * t) * (f x * g x)) ρ := hf.add i1
    have i3 : Integrable (fun x => (t * t) * g x ^ 2) ρ := hg.const_mul _
    rw [h1, integral_add i2 i3, integral_add hf i1, integral_const_mul,
      integral_const_mul] at h0
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- The squared Hellinger distance `∫(√p − √q)² dρ`, written as `∫p + ∫q − 2∫√(pq)`. -/
noncomputable def hellSq (ρ : Measure α) (p q : α → ℝ) : ℝ :=
  ∫ x, p x ∂ρ + ∫ x, q x ∂ρ - 2 * ∫ x, √(p x * q x) ∂ρ

/-- **The Hellinger inequality, root form.** `a`, `b` are the square roots of the two densities.
`(∫h·a² − ∫h·b²)² ≤ 2·(∫a² + ∫b² − 2∫ab)·(∫h²a² + ∫h²b²)`. -/
theorem hell_core (ρ : Measure α) {a b h : α → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hh : Measurable h) (ia : Integrable (fun x => a x ^ 2) ρ)
    (ib : Integrable (fun x => b x ^ 2) ρ)
    (iha : Integrable (fun x => h x ^ 2 * a x ^ 2) ρ)
    (ihb : Integrable (fun x => h x ^ 2 * b x ^ 2) ρ) :
    (∫ x, h x * a x ^ 2 ∂ρ - ∫ x, h x * b x ^ 2 ∂ρ) ^ 2 ≤
      2 * (∫ x, a x ^ 2 ∂ρ + ∫ x, b x ^ 2 ∂ρ - 2 * ∫ x, a x * b x ∂ρ) *
        (∫ x, h x ^ 2 * a x ^ 2 ∂ρ + ∫ x, h x ^ 2 * b x ^ 2 ∂ρ) := by
  have iab0 : Integrable (fun x => a x ^ 2 + b x ^ 2) ρ := ia.add ib
  have ia0 : Integrable (fun x => a x ^ 2 + h x ^ 2 * a x ^ 2) ρ := ia.add iha
  have ib0 : Integrable (fun x => b x ^ 2 + h x ^ 2 * b x ^ 2) ρ := ib.add ihb
  have ih0 : Integrable (fun x => h x ^ 2 * a x ^ 2 + h x ^ 2 * b x ^ 2) ρ := iha.add ihb
  have iab : Integrable (fun x => a x * b x) ρ := by
    refine iab0.mono' (ha.mul hb).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x + b x)]
  have i1a : Integrable (fun x => h x * a x ^ 2) ρ := by
    refine ia0.mono' (hh.mul (ha.pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (h x - 1), sq_nonneg (h x + 1), sq_nonneg (a x)]
  have i1b : Integrable (fun x => h x * b x ^ 2) ρ := by
    refine ib0.mono' (hh.mul (hb.pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (h x - 1), sq_nonneg (h x + 1), sq_nonneg (b x)]
  have ihab : Integrable (fun x => h x ^ 2 * (a x * b x)) ρ := by
    refine ih0.mono' ((hh.pow_const 2).mul (ha.mul hb)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h0 : 0 ≤ h x ^ 2 := sq_nonneg _
    constructor <;> nlinarith [mul_nonneg h0 (sq_nonneg (a x - b x)),
      mul_nonneg h0 (sq_nonneg (a x + b x))]
  set f : α → ℝ := fun x => a x - b x with hf
  set g : α → ℝ := fun x => h x * (a x + b x) with hg
  have ef2 : (fun x => f x ^ 2) = fun x => a x ^ 2 + b x ^ 2 - 2 * (a x * b x) := by
    funext x; simp only [hf]; ring
  have eg2 : (fun x => g x ^ 2) =
      fun x => h x ^ 2 * a x ^ 2 + h x ^ 2 * b x ^ 2 + 2 * (h x ^ 2 * (a x * b x)) := by
    funext x; simp only [hg]; ring
  have efg : (fun x => f x * g x) = fun x => h x * a x ^ 2 - h x * b x ^ 2 := by
    funext x; simp only [hf, hg]; ring
  have if2 : Integrable (fun x => f x ^ 2) ρ := by
    rw [ef2]; exact iab0.sub (iab.const_mul 2)
  have ig2 : Integrable (fun x => g x ^ 2) ρ := by
    rw [eg2]; exact ih0.add (ihab.const_mul 2)
  have ifg : Integrable (fun x => f x * g x) ρ := by
    rw [efg]; exact i1a.sub i1b
  have hcs := cs_sq ρ if2 ig2 ifg
  have e1 : ∫ x, f x * g x ∂ρ = ∫ x, h x * a x ^ 2 ∂ρ - ∫ x, h x * b x ^ 2 ∂ρ := by
    rw [efg, integral_sub i1a i1b]
  have e2 : ∫ x, f x ^ 2 ∂ρ = ∫ x, a x ^ 2 ∂ρ + ∫ x, b x ^ 2 ∂ρ - 2 * ∫ x, a x * b x ∂ρ := by
    rw [ef2, integral_sub iab0 (iab.const_mul 2), integral_add ia ib,
      integral_const_mul]
  have e3 : ∫ x, g x ^ 2 ∂ρ ≤
      2 * (∫ x, h x ^ 2 * a x ^ 2 ∂ρ + ∫ x, h x ^ 2 * b x ^ 2 ∂ρ) := by
    rw [← integral_add iha ihb, ← integral_const_mul]
    refine integral_mono ig2 (ih0.const_mul 2) fun x => ?_
    simp only [hg]
    have h0 : 0 ≤ h x ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h0 (sq_nonneg (a x - b x))]
  have h0 : 0 ≤ ∫ x, f x ^ 2 ∂ρ := integral_nonneg fun x => sq_nonneg _
  rw [e1] at hcs
  rw [← e2]
  calc _ ≤ (∫ x, f x ^ 2 ∂ρ) * ∫ x, g x ^ 2 ∂ρ := hcs
    _ ≤ (∫ x, f x ^ 2 ∂ρ) *
        (2 * (∫ x, h x ^ 2 * a x ^ 2 ∂ρ + ∫ x, h x ^ 2 * b x ^ 2 ∂ρ)) :=
      mul_le_mul_of_nonneg_left e3 h0
    _ = _ := by ring

/-- **The Hellinger inequality, density form.**
`(∫h·p − ∫h·q)² ≤ 2·H²(p, q)·(∫h²p + ∫h²q)`. -/
theorem hell_fn (ρ : Measure α) {p q h : α → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (ip : Integrable p ρ) (iq : Integrable q ρ)
    (hh : Measurable h) (ihp : Integrable (fun x => h x ^ 2 * p x) ρ)
    (ihq : Integrable (fun x => h x ^ 2 * q x) ρ) :
    (∫ x, h x * p x ∂ρ - ∫ x, h x * q x ∂ρ) ^ 2 ≤
      2 * hellSq ρ p q * (∫ x, h x ^ 2 * p x ∂ρ + ∫ x, h x ^ 2 * q x ∂ρ) := by
  have ea : ∀ x, √(p x) ^ 2 = p x := fun x => Real.sq_sqrt (hp0 x)
  have eb : ∀ x, √(q x) ^ 2 = q x := fun x => Real.sq_sqrt (hq0 x)
  have eab : ∀ x, √(p x) * √(q x) = √(p x * q x) := fun x => (Real.sqrt_mul (hp0 x) _).symm
  have h := hell_core ρ (a := fun x => √(p x)) (b := fun x => √(q x)) (h := h) hp.sqrt hq.sqrt hh
    (by simpa only [ea] using ip) (by simpa only [eb] using iq)
    (by simpa only [ea] using ihp) (by simpa only [eb] using ihq)
  simp only [ea, eb, eab] at h
  exact h

/-- `∫ h d(p·ρ) = ∫ h·p dρ`. -/
lemma integral_dens (ρ : Measure α) {p : α → ℝ} (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (h : α → ℝ) :
    ∫ x, h x ∂ρ.withDensity (fun x => ENNReal.ofReal (p x)) = ∫ x, h x * p x ∂ρ := by
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hp0 x), smul_eq_mul]
  ring

/-- **The Hellinger inequality for two means (item 1).** `P = p·ρ`, `Q = q·ρ`:
`(E_P h − E_Q h)² ≤ 2·H²(P, Q)·(E_P h² + E_Q h²)`, with `H² = ∫(√p − √q)² dρ`. -/
theorem hellMean138 (ρ : Measure α) {p q h : α → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (ip : Integrable p ρ) (iq : Integrable q ρ)
    (hh : Measurable h) (ihp : Integrable (fun x => h x ^ 2 * p x) ρ)
    (ihq : Integrable (fun x => h x ^ 2 * q x) ρ) :
    (∫ x, h x ∂ρ.withDensity (fun x => ENNReal.ofReal (p x)) -
        ∫ x, h x ∂ρ.withDensity (fun x => ENNReal.ofReal (q x))) ^ 2 ≤
      2 * hellSq ρ p q *
        (∫ x, h x ^ 2 ∂ρ.withDensity (fun x => ENNReal.ofReal (p x)) +
          ∫ x, h x ^ 2 ∂ρ.withDensity (fun x => ENNReal.ofReal (q x))) := by
  rw [integral_dens ρ hp hp0, integral_dens ρ hq hq0, integral_dens ρ hp hp0,
    integral_dens ρ hq hq0]
  exact hell_fn ρ hp hq hp0 hq0 ip iq hh ihp ihq

/-- `0 ≤ H²`. -/
lemma hellSq_nonneg (ρ : Measure α) {p q : α → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (ip : Integrable p ρ) (iq : Integrable q ρ) :
    0 ≤ hellSq ρ p q := by
  have ipq : Integrable (fun x => p x + q x) ρ := ip.add iq
  have isq : Integrable (fun x => √(p x * q x)) ρ := by
    refine ipq.mono' (hp.mul hq).sqrt.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_mul (hp0 x)]
    have h1 := Real.sq_sqrt (hp0 x)
    have h2 := Real.sq_sqrt (hq0 x)
    nlinarith [sq_nonneg (√(p x) - √(q x)), Real.sqrt_nonneg (p x), Real.sqrt_nonneg (q x)]
  unfold hellSq
  rw [← integral_add ip iq, ← integral_const_mul, ← integral_sub ipq (isq.const_mul 2)]
  refine integral_nonneg fun x => ?_
  change 0 ≤ p x + q x - 2 * √(p x * q x)
  rw [Real.sqrt_mul (hp0 x)]
  have h1 := Real.sq_sqrt (hp0 x)
  have h2 := Real.sq_sqrt (hq0 x)
  nlinarith [sq_nonneg (√(p x) - √(q x))]

/-- **Item 1 for a bounded function**: `P`, `Q` probability measures, `|h| ≤ B`:
`(E_P h − E_Q h)² ≤ 4B²·H²(P, Q)`. -/
theorem hellMean138_bdd (ρ : Measure α) {p q h : α → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (ip : Integrable p ρ) (iq : Integrable q ρ)
    (hp1 : ∫ x, p x ∂ρ = 1) (hq1 : ∫ x, q x ∂ρ = 1)
    (hh : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) :
    (∫ x, h x ∂ρ.withDensity (fun x => ENNReal.ofReal (p x)) -
        ∫ x, h x ∂ρ.withDensity (fun x => ENNReal.ofReal (q x))) ^ 2 ≤
      4 * B ^ 2 * hellSq ρ p q := by
  have hb2 : ∀ x, h x ^ 2 ≤ B ^ 2 := fun x => by
    have := hB x
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have ihp : Integrable (fun x => h x ^ 2 * p x) ρ := by
    refine (ip.const_mul (B ^ 2)).mono' ((hh.pow_const 2).mul hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hp0 x))]
    exact mul_le_mul_of_nonneg_right (hb2 x) (hp0 x)
  have ihq : Integrable (fun x => h x ^ 2 * q x) ρ := by
    refine (iq.const_mul (B ^ 2)).mono' ((hh.pow_const 2).mul hq).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hq0 x))]
    exact mul_le_mul_of_nonneg_right (hb2 x) (hq0 x)
  have h1 := hellMean138 ρ hp hq hp0 hq0 ip iq hh ihp ihq
  rw [integral_dens ρ hp hp0 (fun x => h x ^ 2), integral_dens ρ hq hq0 (fun x => h x ^ 2)] at h1
  have h2 : ∫ x, h x ^ 2 * p x ∂ρ ≤ B ^ 2 := by
    have := integral_mono ihp (ip.const_mul (B ^ 2)) fun x =>
      mul_le_mul_of_nonneg_right (hb2 x) (hp0 x)
    rw [integral_const_mul, hp1, mul_one] at this
    exact this
  have h3 : ∫ x, h x ^ 2 * q x ∂ρ ≤ B ^ 2 := by
    have := integral_mono ihq (iq.const_mul (B ^ 2)) fun x =>
      mul_le_mul_of_nonneg_right (hb2 x) (hq0 x)
    rw [integral_const_mul, hq1, mul_one] at this
    exact this
  have h4 := hellSq_nonneg ρ hp hq hp0 hq0 ip iq
  calc _ ≤ 2 * hellSq ρ p q * (∫ x, h x ^ 2 * p x ∂ρ + ∫ x, h x ^ 2 * q x ∂ρ) := h1
    _ ≤ 2 * hellSq ρ p q * (B ^ 2 + B ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity)
    _ = _ := by ring

end BstLean.Part138

open BstLean.Part138 in
#print axioms hellMean138
open BstLean.Part138 in
#print axioms hellMean138_bdd
