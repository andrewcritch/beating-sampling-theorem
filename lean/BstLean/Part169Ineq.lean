import BstLean.Part169Price

/-!
# Part 169 (file `Ineq`): integral inequalities on a set of mass at most one

No proof is left open; no `native_decide` or `axiom` is used.

These are the Minkowski, Hölder, Jensen and Markov steps of `theorem7-08-bias.tex`
(formulas `t7:p08:scale` and `t7:p08:mass`), in the form that the scale price needs. Each proof
uses a pointwise weighted AM–GM or convexity inequality and integrates it; no `L^p` space is used.

* `amgm13`: `4us³ ≤ u⁴ + 3s⁴` for `u, s ≥ 0`.
* `int_sq_add`: Minkowski in `L²`: `∫x² ≤ A²`, `∫y² ≤ B²` give `∫(x + y)² ≤ (A + B)²`.
* `int_pow6_add`: Minkowski in `L⁶` for nonnegative `x`, `y`.
* `int_pow6_of_pow8`: Jensen `L⁸ → L⁶` on a set of mass at most one.
* `int_sq_mul_le`: Hölder `(4, 4)`: `∫f⁴ ≤ H⁴`, `∫y⁴ ≤ a⁴` give `∫f²y² ≤ H²a²`.
* `int_pow6_mul_le`: Hölder `(24, 8)`: `∫f²⁴ ≤ H²⁴`, `∫y⁸ ≤ a⁸` give `∫f⁶y⁶ ≤ H⁶a⁶`.
* `markov_on`: `μ(K ∩ {c ≤ f}) ≤ (∫_K f)/c` for `f ≥ 0`, `c > 0`.
-/

namespace BstLean.Part169

open MeasureTheory Real

/-- `4us³ ≤ u⁴ + 3s⁴` for `u, s ≥ 0`: `u⁴ + 3s⁴ − 4us³ = (u − s)²(u² + 2us + 3s²)`. -/
lemma amgm13 {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) : 4 * u * s ^ 3 ≤ u ^ 4 + 3 * s ^ 4 := by
  have hq : 0 ≤ u ^ 2 + 2 * u * s + 3 * s ^ 2 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (u - s)) hq]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α}

/-- **Minkowski in `L²`** (two terms). -/
theorem int_sq_add {x y : α → ℝ} (mx : AEStronglyMeasurable x (μ.restrict K))
    (my : AEStronglyMeasurable y (μ.restrict K))
    (ix : IntegrableOn (fun a => x a ^ 2) K μ) (iy : IntegrableOn (fun a => y a ^ 2) K μ)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : ∫ a in K, x a ^ 2 ∂μ ≤ A ^ 2)
    (hy : ∫ a in K, y a ^ 2 ∂μ ≤ B ^ 2) :
    IntegrableOn (fun a => (x a + y a) ^ 2) K μ ∧ ∫ a in K, (x a + y a) ^ 2 ∂μ ≤ (A + B) ^ 2 := by
  have hpt : ∀ a, (x a + y a) ^ 2 ≤ (A + B) * (x a ^ 2 / A + y a ^ 2 / B) := by
    intro a
    have e : (A + B) * (x a ^ 2 / A + y a ^ 2 / B) - (x a + y a) ^ 2 =
        (B * x a - A * y a) ^ 2 / (A * B) := by field_simp; ring
    have : 0 ≤ (B * x a - A * y a) ^ 2 / (A * B) := by positivity
    linarith
  have i3 : IntegrableOn (fun a => (A + B) * (x a ^ 2 / A + y a ^ 2 / B)) K μ :=
    ((ix.div_const _).add (iy.div_const _)).const_mul _
  have i1 : IntegrableOn (fun a => (x a + y a) ^ 2) K μ := by
    refine Integrable.mono' i3 ((mx.add my).pow 2) (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt a
  refine ⟨i1, (integral_mono i1 i3 hpt).trans ?_⟩
  rw [integral_const_mul, integral_add (ix.div_const _) (iy.div_const _), integral_div,
    integral_div]
  have h1 : (∫ a in K, x a ^ 2 ∂μ) / A ≤ A := by rw [div_le_iff₀ hA]; nlinarith
  have h2 : (∫ a in K, y a ^ 2 ∂μ) / B ≤ B := by rw [div_le_iff₀ hB]; nlinarith
  have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : (0:ℝ) ≤ A + B)
  nlinarith

/-- **Minkowski in `L⁶`** (two nonnegative terms). -/
theorem int_pow6_add {x y : α → ℝ} (mx : AEStronglyMeasurable x (μ.restrict K))
    (my : AEStronglyMeasurable y (μ.restrict K)) (hx0 : ∀ a, 0 ≤ x a) (hy0 : ∀ a, 0 ≤ y a)
    (ix : IntegrableOn (fun a => x a ^ 6) K μ) (iy : IntegrableOn (fun a => y a ^ 6) K μ)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : ∫ a in K, x a ^ 6 ∂μ ≤ A ^ 6)
    (hy : ∫ a in K, y a ^ 6 ∂μ ≤ B ^ 6) :
    IntegrableOn (fun a => (x a + y a) ^ 6) K μ ∧ ∫ a in K, (x a + y a) ^ 6 ∂μ ≤ (A + B) ^ 6 := by
  have hAB : 0 < A + B := add_pos hA hB
  have hpt : ∀ a, (x a + y a) ^ 6 ≤ (A + B) ^ 5 * (x a ^ 6 / A ^ 5 + y a ^ 6 / B ^ 5) := by
    intro a
    set l := A / (A + B) with hl
    have hl0 : 0 < l := div_pos hA hAB
    have hl1 : 0 < 1 - l := by rw [hl]; rw [sub_pos, div_lt_one hAB]; linarith
    have e1 : 1 - l = B / (A + B) := by rw [hl]; field_simp; ring
    have hc := (convexOn_pow (𝕜 := ℝ) 6).2 (Set.mem_Ici.mpr (div_nonneg (hx0 a) hl0.le))
      (Set.mem_Ici.mpr (div_nonneg (hy0 a) hl1.le)) hl0.le hl1.le (by ring)
    simp only [smul_eq_mul] at hc
    have e2 : l * (x a / l) + (1 - l) * (y a / (1 - l)) = x a + y a := by
      field_simp
    rw [e2] at hc
    refine hc.trans (le_of_eq ?_)
    rw [e1, hl]
    field_simp
  have i3 : IntegrableOn (fun a => (A + B) ^ 5 * (x a ^ 6 / A ^ 5 + y a ^ 6 / B ^ 5)) K μ :=
    ((ix.div_const _).add (iy.div_const _)).const_mul _
  have i1 : IntegrableOn (fun a => (x a + y a) ^ 6) K μ := by
    refine Integrable.mono' i3 ((mx.add my).pow 6) (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := hx0 a; have := hy0 a; positivity)]
    exact hpt a
  refine ⟨i1, (integral_mono i1 i3 hpt).trans ?_⟩
  rw [integral_const_mul, integral_add (ix.div_const _) (iy.div_const _), integral_div,
    integral_div]
  have h1 : (∫ a in K, x a ^ 6 ∂μ) / A ^ 5 ≤ A := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h2 : (∫ a in K, y a ^ 6 ∂μ) / B ^ 5 ≤ B := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : (0:ℝ) ≤ (A + B) ^ 5)
  nlinarith

/-- **Jensen `L⁸ → L⁶`** on a set of mass at most one. -/
theorem int_pow6_of_pow8 [IsFiniteMeasure μ] (hK1 : μ.real K ≤ 1) {h : α → ℝ} {a : ℝ} (ha : 0 < a)
    (i6 : IntegrableOn (fun x => h x ^ 6) K μ) (i8 : IntegrableOn (fun x => h x ^ 8) K μ)
    (h8 : ∫ x in K, h x ^ 8 ∂μ ≤ a ^ 8) : ∫ x in K, h x ^ 6 ∂μ ≤ a ^ 6 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hpt : ∀ x, h x ^ 6 ≤ 1 / 4 * a ^ 6 + 3 / 4 * (h x ^ 8 / a ^ 2) := by
    intro x
    have hm := amgm13 (sq_nonneg a) (sq_nonneg (h x))
    rw [show 1 / 4 * a ^ 6 + 3 / 4 * (h x ^ 8 / a ^ 2) = (a ^ 8 + 3 * h x ^ 8) / (4 * a ^ 2) by
      field_simp, le_div_iff₀ (by positivity)]
    nlinarith
  have i3 : IntegrableOn (fun x => 1 / 4 * a ^ 6 + 3 / 4 * (h x ^ 8 / a ^ 2)) K μ :=
    (integrable_const _).add ((i8.div_const _).const_mul _)
  refine (integral_mono i6 i3 hpt).trans ?_
  rw [integral_add (integrable_const _) ((i8.div_const _).const_mul _), integral_const,
    smul_eq_mul, measureReal_restrict_apply_univ, integral_const_mul, integral_div]
  have h1 : μ.real K * (1 / 4 * a ^ 6) ≤ 1 / 4 * a ^ 6 := by
    have := mul_le_mul_of_nonneg_right hK1 (by positivity : (0:ℝ) ≤ 1 / 4 * a ^ 6)
    linarith
  have h2 : (∫ x in K, h x ^ 8 ∂μ) / a ^ 2 ≤ a ^ 6 := by
    rw [div_le_iff₀ ha2]; nlinarith
  nlinarith

/-- **Hölder `(4, 4)`** for squares. -/
theorem int_sq_mul_le {f y : α → ℝ} (if4 : IntegrableOn (fun x => f x ^ 4) K μ)
    (iy4 : IntegrableOn (fun x => y x ^ 4) K μ)
    (ify : IntegrableOn (fun x => f x ^ 2 * y x ^ 2) K μ) {H a : ℝ} (hH : 0 < H) (ha : 0 < a)
    (hf : ∫ x in K, f x ^ 4 ∂μ ≤ H ^ 4) (hy : ∫ x in K, y x ^ 4 ∂μ ≤ a ^ 4) :
    ∫ x in K, f x ^ 2 * y x ^ 2 ∂μ ≤ H ^ 2 * a ^ 2 := by
  set t := a ^ 2 / H ^ 2 with ht
  have ht0 : 0 < t := by positivity
  have hpt : ∀ x, f x ^ 2 * y x ^ 2 ≤ t / 2 * f x ^ 4 + 1 / (2 * t) * y x ^ 4 := by
    intro x
    have e : t / 2 * f x ^ 4 + 1 / (2 * t) * y x ^ 4 - f x ^ 2 * y x ^ 2 =
        (t * f x ^ 2 - y x ^ 2) ^ 2 / (2 * t) := by field_simp; ring
    have : 0 ≤ (t * f x ^ 2 - y x ^ 2) ^ 2 / (2 * t) := by positivity
    linarith
  have i3 : IntegrableOn (fun x => t / 2 * f x ^ 4 + 1 / (2 * t) * y x ^ 4) K μ :=
    (if4.const_mul _).add (iy4.const_mul _)
  refine (integral_mono ify i3 hpt).trans ?_
  rw [integral_add (if4.const_mul _) (iy4.const_mul _), integral_const_mul, integral_const_mul]
  have h1 := mul_le_mul_of_nonneg_left hf (by positivity : (0:ℝ) ≤ t / 2)
  have h2 := mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ 1 / (2 * t))
  have e : t / 2 * H ^ 4 + 1 / (2 * t) * a ^ 4 = H ^ 2 * a ^ 2 := by
    rw [ht]; field_simp; ring
  linarith

/-- **Hölder `(24, 8)`** for sixth powers. -/
theorem int_pow6_mul_le {f y : α → ℝ} (if24 : IntegrableOn (fun x => f x ^ 24) K μ)
    (iy8 : IntegrableOn (fun x => y x ^ 8) K μ)
    (ify : IntegrableOn (fun x => f x ^ 6 * y x ^ 6) K μ) {H a : ℝ} (hH : 0 < H) (ha : 0 < a)
    (hf : ∫ x in K, f x ^ 24 ∂μ ≤ H ^ 24) (hy : ∫ x in K, y x ^ 8 ∂μ ≤ a ^ 8) :
    ∫ x in K, f x ^ 6 * y x ^ 6 ∂μ ≤ H ^ 6 * a ^ 6 := by
  set t := H ^ 6 / a ^ 2 with ht
  have ht0 : 0 < t := by positivity
  -- `u s³ ≤ (u⁴ + 3 s⁴)/4` with `u = f⁶`, `s = t y²`
  have hpt : ∀ x, f x ^ 6 * y x ^ 6 ≤ 1 / (4 * t ^ 3) * f x ^ 24 + 3 * t / 4 * y x ^ 8 := by
    intro x
    have hm := amgm13 (u := f x ^ 6) (s := t * y x ^ 2) (by positivity) (by positivity)
    have e : 1 / (4 * t ^ 3) * f x ^ 24 + 3 * t / 4 * y x ^ 8 =
        ((f x ^ 6) ^ 4 + 3 * (t * y x ^ 2) ^ 4) / (4 * t ^ 3) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith
  have i3 : IntegrableOn (fun x => 1 / (4 * t ^ 3) * f x ^ 24 + 3 * t / 4 * y x ^ 8) K μ :=
    (if24.const_mul _).add (iy8.const_mul _)
  refine (integral_mono ify i3 hpt).trans ?_
  rw [integral_add (if24.const_mul _) (iy8.const_mul _), integral_const_mul, integral_const_mul]
  have h1 := mul_le_mul_of_nonneg_left hf (by positivity : (0:ℝ) ≤ 1 / (4 * t ^ 3))
  have h2 := mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ 3 * t / 4)
  have e : 1 / (4 * t ^ 3) * H ^ 24 + 3 * t / 4 * a ^ 8 = H ^ 6 * a ^ 6 := by
    rw [ht]; field_simp; ring
  linarith

/-- **Markov on a set**: `μ(K ∩ {c ≤ f}) ≤ (∫_K f)/c`. -/
theorem markov_on (hK : MeasurableSet K) {f : α → ℝ} (mf : Measurable f)
    (hf0 : ∀ a ∈ K, 0 ≤ f a) (hfi : IntegrableOn f K μ) {c : ℝ} (hc : 0 < c) :
    μ.real (K ∩ {a | c ≤ f a}) ≤ (∫ a in K, f a ∂μ) / c := by
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := μ.restrict K)
    ((ae_restrict_iff' hK).mpr (Filter.Eventually.of_forall hf0)) hfi c
  have hs : MeasurableSet {a | c ≤ f a} := measurableSet_le measurable_const mf
  rw [measureReal_restrict_apply hs, Set.inter_comm] at hm
  rw [le_div_iff₀ hc]; linarith

end BstLean.Part169
