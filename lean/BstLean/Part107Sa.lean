import BstLean.Part107Defs

/-!
# Part 107 S(a): the abstract moment computation for one fixed `W`

A function `f θ u` (in the instance: `ℓ·A(x_W(u))`, `θ = (A, ℓ)`) with the Wick identities
`E f(u₁)f(u₂) = a κ(u₁,u₂)` and
`E f(u₁)f(u₂)f(u₃)f(u₄) = b(κ₁₂κ₃₄ + κ₁₃κ₂₄ + κ₁₄κ₂₃)`.
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory

set_option linter.unusedSectionVars false

/-- A bounded measurable function is integrable for a finite measure. -/
lemma bm_int {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ}
    (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ fun x => by simpa using hC x)

lemma abs_int_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {g : α → ℝ} (C : ℝ) (hC : ∀ x, |g x| ≤ C) : |∫ x, g x ∂μ| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := C)
    (ae_of_all _ fun x => by simpa using hC x)
  simpa using h

lemma sq_int_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {g : α → ℝ} (hg : Integrable g μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ x, (g x - ∫ y, g y ∂μ) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have h1 : ∫ x, (g x - ∫ y, g y ∂μ) ^ 2 ∂μ = ∫ x, g x ^ 2 ∂μ - (∫ x, g x ∂μ) ^ 2 := by
    set m := ∫ y, g y ∂μ with hm
    have e : (fun x => (g x - m) ^ 2) = fun x => g x ^ 2 - 2 * m * g x + m ^ 2 := by
      funext x; ring
    have hs : Integrable (fun x => g x ^ 2 - 2 * m * g x) μ := hg2.sub (hg.const_mul _)
    have hc : Integrable (fun x => 2 * m * g x) μ := hg.const_mul _
    rw [e, integral_add hs (integrable_const _),
      integral_sub hg2 hc, integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [← hm]; ring
  linarith

variable {U Θ : Type*} [MeasurableSpace U] [MeasurableSpace Θ]

/-- The abstract setting for one fixed `W`. -/
structure Setup (γ : Measure Θ) (f : Θ → U → ℝ) (Q : Θ → ℝ) (κ : U → U → ℝ) (a b C : ℝ) :
    Prop where
  hf : Measurable (fun p : Θ × U => f p.1 p.2)
  hQm : Measurable Q
  hQ0 : ∀ θ, 0 ≤ Q θ
  hQ4 : Integrable (fun θ => Q θ ^ 4) γ
  hfQ : ∀ θ u, |f θ u| ≤ Q θ
  hκ : Measurable (fun p : U × U => κ p.1 p.2)
  hκC : ∀ u u', |κ u u'| ≤ C
  hsymm : ∀ u u', κ u u' = κ u' u
  h2 : ∀ u1 u2, ∫ θ, f θ u1 * f θ u2 ∂γ = a * κ u1 u2
  h4 : ∀ u1 u2 u3 u4, ∫ θ, f θ u1 * f θ u2 * f θ u3 * f θ u4 ∂γ =
    b * (κ u1 u2 * κ u3 u4 + κ u1 u3 * κ u2 u4 + κ u1 u4 * κ u2 u3)

/-- `∫ f(θ, s p) f(θ, t p) dρ(p)`. -/
noncomputable def Mp (f : Θ → U → ℝ) {S : Type*} [MeasurableSpace S] (ρ : Measure S)
    (s t : S → U) (θ : Θ) : ℝ :=
  ∫ p, f θ (s p) * f θ (t p) ∂ρ

section
variable {γ : Measure Θ} [IsProbabilityMeasure γ] {f : Θ → U → ℝ} {Q : Θ → ℝ} {κ : U → U → ℝ}
  {a b C : ℝ} (H : Setup γ f Q κ a b C)
include H

lemma Setup.km {α : Type*} [MeasurableSpace α] {g h : α → U} (hg : Measurable g)
    (hh : Measurable h) : Measurable (fun z => κ (g z) (h z)) :=
  H.hκ.comp (hg.prodMk hh)

lemma Setup.fm {α : Type*} [MeasurableSpace α] {g : α → Θ} {h : α → U} (hg : Measurable g)
    (hh : Measurable h) : Measurable (fun z => f (g z) (h z)) :=
  H.hf.comp (hg.prodMk hh)

lemma Setup.hQ2 : Integrable (fun θ => Q θ ^ 2) γ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add H.hQ4)
    (H.hQm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  show _ ≤ 1 + Q θ ^ 4
  nlinarith [sq_nonneg (Q θ ^ 2 - 1), sq_nonneg (Q θ ^ 2)]

variable {S : Type*} [MeasurableSpace S] {ρ : Measure S} [IsProbabilityMeasure ρ] {s t : S → U}
  (hs : Measurable s) (ht : Measurable t)
include hs ht

lemma Setup.Mp_meas : Measurable (Mp f ρ s t) := by
  have h : Measurable (fun z : Θ × S => f z.1 (s z.2) * f z.1 (t z.2)) :=
    (H.fm measurable_fst (hs.comp measurable_snd)).mul
      (H.fm measurable_fst (ht.comp measurable_snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

lemma Setup.Mp_abs (θ : Θ) : |Mp f ρ s t θ| ≤ Q θ ^ 2 := by
  refine abs_int_le _ fun p => ?_
  rw [abs_mul, sq]
  exact mul_le_mul (H.hfQ _ _) (H.hfQ _ _) (abs_nonneg _) (H.hQ0 _)

lemma Setup.Mp_int : Integrable (Mp f ρ s t) γ :=
  Integrable.mono' H.hQ2 (H.Mp_meas hs ht).aestronglyMeasurable
    (ae_of_all _ fun θ => by simpa using H.Mp_abs hs ht θ)

lemma Setup.Mp_two : ∫ θ, Mp f ρ s t θ ∂γ = a * ∫ p, κ (s p) (t p) ∂ρ := by
  unfold Mp
  have hint : Integrable (Function.uncurry fun θ p => f θ (s p) * f θ (t p)) (γ.prod ρ) := by
    refine Integrable.mono' (H.hQ2.comp_fst ρ) ?_ (ae_of_all _ fun z => ?_)
    · exact ((H.fm measurable_fst (hs.comp measurable_snd)).mul
        (H.fm measurable_fst (ht.comp measurable_snd))).aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs]
      rw [abs_mul, sq]
      exact mul_le_mul (H.hfQ _ _) (H.hfQ _ _) (abs_nonneg _) (H.hQ0 _)
  rw [integral_integral_swap hint]
  simp_rw [H.h2]
  rw [integral_const_mul]

end

section
variable {γ : Measure Θ} [IsProbabilityMeasure γ] {f : Θ → U → ℝ} {Q : Θ → ℝ} {κ : U → U → ℝ}
  {a b C : ℝ} (H : Setup γ f Q κ a b C)
  {S : Type*} [MeasurableSpace S] {ρ : Measure S} [IsProbabilityMeasure ρ] {s t : S → U}
  (hs : Measurable s) (ht : Measurable t)
  {S' : Type*} [MeasurableSpace S'] {ρ' : Measure S'} [IsProbabilityMeasure ρ'] {s' t' : S' → U}
  (hs' : Measurable s') (ht' : Measurable t')
include H hs ht hs' ht'

lemma Setup.MM_int : Integrable (fun θ => Mp f ρ s t θ * Mp f ρ' s' t' θ) γ := by
  refine Integrable.mono' H.hQ4 ((H.Mp_meas hs ht).mul (H.Mp_meas hs' ht')).aestronglyMeasurable
    (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := H.Mp_abs hs ht (ρ := ρ) θ
  have h2 := H.Mp_abs hs' ht' (ρ := ρ') θ
  calc |Mp f ρ s t θ| * |Mp f ρ' s' t' θ| ≤ Q θ ^ 2 * Q θ ^ 2 :=
        mul_le_mul h1 h2 (abs_nonneg _) (sq_nonneg _)
    _ = Q θ ^ 4 := by ring

lemma Setup.Mp_four : ∫ θ, Mp f ρ s t θ * Mp f ρ' s' t' θ ∂γ =
    b * ((∫ p, κ (s p) (t p) ∂ρ) * (∫ p', κ (s' p') (t' p') ∂ρ') +
      (∫ p, ∫ p', κ (s p) (s' p') * κ (t p) (t' p') ∂ρ' ∂ρ) +
      (∫ p, ∫ p', κ (s p) (t' p') * κ (t p) (s' p') ∂ρ' ∂ρ)) := by
  have e1 : ∀ θ, Mp f ρ s t θ * Mp f ρ' s' t' θ =
      ∫ z, f θ (s z.1) * f θ (t z.1) * f θ (s' z.2) * f θ (t' z.2) ∂(ρ.prod ρ') := by
    intro θ
    unfold Mp
    rw [← integral_prod_mul]
    simp only [mul_assoc]
  simp_rw [e1]
  have hint : Integrable (Function.uncurry fun θ (z : S × S') =>
      f θ (s z.1) * f θ (t z.1) * f θ (s' z.2) * f θ (t' z.2)) (γ.prod (ρ.prod ρ')) := by
    refine Integrable.mono' (H.hQ4.comp_fst (ρ.prod ρ')) ?_ (ae_of_all _ fun z => ?_)
    · exact ((((H.fm measurable_fst (hs.comp (measurable_fst.comp measurable_snd))).mul
        (H.fm measurable_fst (ht.comp (measurable_fst.comp measurable_snd)))).mul
        (H.fm measurable_fst (hs'.comp (measurable_snd.comp measurable_snd)))).mul
        (H.fm measurable_fst (ht'.comp (measurable_snd.comp measurable_snd)))).aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_mul]
      have q0 := H.hQ0 z.1
      calc _ ≤ Q z.1 * Q z.1 * Q z.1 * Q z.1 := by
            refine mul_le_mul (mul_le_mul (mul_le_mul (H.hfQ _ _) (H.hfQ _ _) (abs_nonneg _) q0)
              (H.hfQ _ _) (abs_nonneg _) (by positivity)) (H.hfQ _ _) (abs_nonneg _)
              (by positivity)
        _ = Q z.1 ^ 4 := by ring
  rw [integral_integral_swap hint]
  simp_rw [H.h4]
  have m1 : Measurable (fun z : S × S' => κ (s z.1) (t z.1) * κ (s' z.2) (t' z.2)) :=
    (H.km (hs.comp measurable_fst) (ht.comp measurable_fst)).mul
      (H.km (hs'.comp measurable_snd) (ht'.comp measurable_snd))
  have m2 : Measurable (fun z : S × S' => κ (s z.1) (s' z.2) * κ (t z.1) (t' z.2)) :=
    (H.km (hs.comp measurable_fst) (hs'.comp measurable_snd)).mul
      (H.km (ht.comp measurable_fst) (ht'.comp measurable_snd))
  have m3 : Measurable (fun z : S × S' => κ (s z.1) (t' z.2) * κ (t z.1) (s' z.2)) :=
    (H.km (hs.comp measurable_fst) (ht'.comp measurable_snd)).mul
      (H.km (ht.comp measurable_fst) (hs'.comp measurable_snd))
  have bd : ∀ x y x' y' : U, |κ x y * κ x' y'| ≤ |C| * |C| := fun x y x' y' => by
    rw [abs_mul]
    exact mul_le_mul ((H.hκC _ _).trans (le_abs_self _)) ((H.hκC _ _).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  have i1 := bm_int (μ := ρ.prod ρ') m1 _ fun z => bd _ _ _ _
  have i2 := bm_int (μ := ρ.prod ρ') m2 _ fun z => bd _ _ _ _
  have i3 := bm_int (μ := ρ.prod ρ') m3 _ fun z => bd _ _ _ _
  have i12 : Integrable (fun z : S × S' => κ (s z.1) (t z.1) * κ (s' z.2) (t' z.2) +
      κ (s z.1) (s' z.2) * κ (t z.1) (t' z.2)) (ρ.prod ρ') := i1.add i2
  rw [integral_const_mul, integral_add i12 i3, integral_add i1 i2,
    integral_prod_mul (fun p => κ (s p) (t p)) (fun p' => κ (s' p') (t' p')),
    integral_prod _ i2, integral_prod _ i3]

end

end BstLean.Part107
