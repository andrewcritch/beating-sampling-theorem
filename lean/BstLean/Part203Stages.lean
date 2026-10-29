import BstLean.Part203Composition

/-! Part 203: free root composition and dimension normalization. -/
namespace BstLean.Part203
open MeasureTheory Real BstLean.Part156 BstLean.Part196

lemma world_scale {n c τ v₀ : ℝ} (hn : 0 < n) :
    worldK (c / n) (n * τ) v₀ = n * worldK c τ v₀ ∧
    worldC (c / n) (n * τ) v₀ = n * worldC c τ v₀ := by
  have he : (n * τ) * (c / n) = τ * c := by field_simp
  constructor
  · unfold worldK
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  · unfold worldC tangentC
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

lemma exactRhs_scale {n C K α β Q f : ℝ} (hn : 0 < n) :
    exactRhs (n * C) (n * K) α β Q (f / n) = n * exactRhs C K α β Q f := by
  have he : f / n * (n * K) * α = f * K * α := by field_simp
  unfold exactRhs
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma tgRhs_scale {n C K α β Q f u₀ : ℝ} (hn : 0 < n) :
    tgRhs (n * C) (n * K) α β Q (f / n) u₀ = n * tgRhs C K α β Q f u₀ := by
  have he : f / n * (n * K) * α = f * K * α := by field_simp
  unfold tgRhs tangentC
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

section Stages
variable {ΩW ΩA : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩA]

/-- The affine comparison is dimension-free; normalized exponents retain the factor n. -/
theorem normalized_composition (μW : Measure ΩW) (μA : Measure ΩA)
    [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    {p : ΩW × ΩA → ℝ} (hm : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (h1 : ∀ x, p x ≤ 1) {P : ΩA → ℝ} (hPm : Measurable P)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {n c f τ v₀ α β : ℝ} (hn : 0 < n) (hc : 0 < c) (hf : 0 < f)
    (hv₀ : 0 < 1 + v₀ * (exp (τ * c) - 1))
    (hW : ∀ ωA, ExactPrimitive μW (fun ωW => p (ωW, ωA)) (c / n))
    (hA : ExactPrimitive μA P (f / n))
    (hcmp : ∀ ωA, worldK c τ v₀ * (∫ ωW, p (ωW, ωA) ∂μW) ≤
      worldK c τ v₀ * (α * P ωA + β)) :
    ∫ ω, exp (n * τ * p ω) ∂(μW.prod μA) ≤
      exp (n * exactRhs (worldC c τ v₀) (worldK c τ v₀) α β (∫ ωA, P ωA ∂μA) f) := by
  have he : (n * τ) * (c / n) = τ * c := by field_simp
  have hs := world_scale (c := c) (τ := τ) (v₀ := v₀) hn
  have hcmp' : ∀ ωA, worldK (c / n) (n * τ) v₀ * (∫ ωW, p (ωW, ωA) ∂μW) ≤
      worldK (c / n) (n * τ) v₀ * (α * P ωA + β) := by
    intro ωA
    rw [hs.1]
    have := mul_le_mul_of_nonneg_left (hcmp ωA) hn.le
    simpa only [mul_assoc] using this
  have h := exact_composition μW μA hm h0 h1 hPm hP0 hP1
    (div_pos hc hn) (div_pos hf hn) (by rwa [he]) hW hA hcmp'
  rwa [hs.1, hs.2, exactRhs_scale hn] at h

/-- The paper's normalized logarithmic composition, with an explicit signed comparison. -/
theorem normalized_log_composition (μW : Measure ΩW) (μA : Measure ΩA)
    [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    {p : ΩW × ΩA → ℝ} (hm : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (h1 : ∀ x, p x ≤ 1) {P : ΩA → ℝ} (hPm : Measurable P)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {n c f τ v₀ α β : ℝ} (hn : 0 < n) (hc : 0 < c) (hf : 0 < f)
    (hv₀ : 0 < 1 + v₀ * (exp (τ * c) - 1))
    (hW : ∀ ωA, ExactPrimitive μW (fun ωW => p (ωW, ωA)) (c / n))
    (hA : ExactPrimitive μA P (f / n))
    (hcmp : ∀ ωA, worldK c τ v₀ * (∫ ωW, p (ωW, ωA) ∂μW) ≤
      worldK c τ v₀ * (α * P ωA + β)) :
    log (∫ ω, exp (n * τ * p ω) ∂(μW.prod μA)) / n ≤
      exactRhs (worldC c τ v₀) (worldK c τ v₀) α β (∫ ωA, P ωA ∂μA) f := by
  have h := normalized_composition μW μA hm h0 h1 hPm hP0 hP1 hn hc hf hv₀ hW hA hcmp
  have hl := log_le_log (integral_exp_pos (integrable_exp_mul _ hm h0 h1 _)) h
  rw [log_exp] at hl
  apply (div_le_iff₀ hn).mpr
  simpa [mul_comm] using hl

/-- TG uses two fixed logarithmic tangents, with no linearization at zero. -/
theorem TG (μW : Measure ΩW) (μA : Measure ΩA)
    [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    {p : ΩW × ΩA → ℝ} (hm : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (h1 : ∀ x, p x ≤ 1) {P : ΩA → ℝ} (hPm : Measurable P)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {n c f τ v₀ α β u₀ : ℝ} (hn : 0 < n) (hc : 0 < c) (hf : 0 < f)
    (hv₀ : 0 < 1 + v₀ * (exp (τ * c) - 1)) (hu₀ : -1 < u₀)
    (hW : ∀ ωA, ExactPrimitive μW (fun ωW => p (ωW, ωA)) (c / n))
    (hA : ExactPrimitive μA P (f / n))
    (hcmp : ∀ ωA, worldK c τ v₀ * (∫ ωW, p (ωW, ωA) ∂μW) ≤
      worldK c τ v₀ * (α * P ωA + β)) :
    log (∫ ω, exp (n * τ * p ω) ∂(μW.prod μA)) / n ≤
      tgRhs (worldC c τ v₀) (worldK c τ v₀) α β (∫ ωA, P ωA ∂μA) f u₀ := by
  obtain ⟨hq0, hq1⟩ := BstLean.Part157.integral_mem_01 μA hPm hP0 hP1
  exact (normalized_log_composition μW μA hm h0 h1 hPm hP0 hP1 hn hc hf
    hv₀ hW hA hcmp).trans (exact_le_tg hf hq0 hq1 hu₀)

theorem free_plus_composition (μW : Measure ΩW) (μA : Measure ΩA)
    [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    {p : ΩW × ΩA → ℝ} (hm : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (h1 : ∀ x, p x ≤ 1) {P : ΩA → ℝ} (hPm : Measurable P)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {n c f τ v₀ H r : ℝ} (hn : 0 < n) (hc : 0 < c) (hf : 0 < f)
    (hτ : 0 < τ) (hH : 0 ≤ H) (hr : 0 < r)
    (hv₀ : 0 < 1 + v₀ * (exp (τ * c) - 1))
    (hW : ∀ ωA, ExactPrimitive μW (fun ωW => p (ωW, ωA)) (c / n))
    (hA : ExactPrimitive μA P (f / n))
    (hR : ∀ ωA, |√(∫ ωW, p (ωW, ωA) ∂μW) - √(P ωA)| ≤ H) :
    ∫ ω, exp (n * τ * p ω) ∂(μW.prod μA) ≤
      exp (n * exactRhs (worldC c τ v₀) (worldK c τ v₀)
        (1 + H / r) (H * r + H ^ 2) (∫ ωA, P ωA ∂μA) f) := by
  apply normalized_composition μW μA hm h0 h1 hPm hP0 hP1 hn hc hf hv₀ hW hA
  intro ωA
  apply mul_le_mul_of_nonneg_left _ (worldK_pos hc hτ hv₀).le
  simpa [add_assoc] using
    root_upper (integral_nonneg (fun _ => h0 _)) (hP0 ωA) hH hr (hR ωA)

theorem free_minus_composition (μW : Measure ΩW) (μA : Measure ΩA)
    [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    {p : ΩW × ΩA → ℝ} (hm : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (h1 : ∀ x, p x ≤ 1) {P : ΩA → ℝ} (hPm : Measurable P)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {n c f τ v₀ H r : ℝ} (hn : 0 < n) (hc : 0 < c) (hf : 0 < f)
    (hτ : τ < 0) (hH : 0 ≤ H) (hr : H < r)
    (hv₀ : 0 < 1 + v₀ * (exp (τ * c) - 1))
    (hW : ∀ ωA, ExactPrimitive μW (fun ωW => p (ωW, ωA)) (c / n))
    (hA : ExactPrimitive μA P (f / n))
    (hR : ∀ ωA, |√(∫ ωW, p (ωW, ωA) ∂μW) - √(P ωA)| ≤ H) :
    ∫ ω, exp (n * τ * p ω) ∂(μW.prod μA) ≤
      exp (n * exactRhs (worldC c τ v₀) (worldK c τ v₀)
        (1 - H / r) (-H * r + H ^ 2) (∫ ωA, P ωA ∂μA) f) := by
  apply normalized_composition μW μA hm h0 h1 hPm hP0 hP1 hn hc hf hv₀ hW hA
  intro ωA
  apply mul_le_mul_of_nonpos_left _ (worldK_neg hc hτ hv₀).le
  have := root_lower (integral_nonneg (fun _ => h0 _)) (hP0 ωA) hH hr (hR ωA)
  simpa [sub_eq_add_neg, add_assoc] using this

def FreeCPR {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → ℝ)
    (n c f H Q : ℝ) : Prop :=
  (∀ τ v₀ r : ℝ, 0 < τ → 0 ≤ v₀ → v₀ ≤ 1 → 0 < r →
    ∫ ω, exp (n * τ * p ω) ∂μ ≤
      exp (n * exactRhs (worldC c τ v₀) (worldK c τ v₀)
        (1 + H / r) (H * r + H ^ 2) Q f)) ∧
  (∀ τ v₀ r : ℝ, τ < 0 → 0 ≤ v₀ → v₀ ≤ 1 → H < r →
    ∫ ω, exp (n * τ * p ω) ∂μ ≤
      exp (n * exactRhs (worldC c τ v₀) (worldK c τ v₀)
        (1 - H / r) (-H * r + H ^ 2) Q f))

theorem free_cpr_of_stages (μW : Measure ΩW) (μA : Measure ΩA)
    [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    {p : ΩW × ΩA → ℝ} (hm : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (h1 : ∀ x, p x ≤ 1) {P : ΩA → ℝ} (hPm : Measurable P)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {n c f H : ℝ} (hn : 0 < n) (hc : 0 < c) (hf : 0 < f) (hH : 0 ≤ H)
    (hW : ∀ ωA, ExactPrimitive μW (fun ωW => p (ωW, ωA)) (c / n))
    (hA : ExactPrimitive μA P (f / n))
    (hR : ∀ ωA, |√(∫ ωW, p (ωW, ωA) ∂μW) - √(P ωA)| ≤ H) :
    FreeCPR (μW.prod μA) p n c f H (∫ ωA, P ωA ∂μA) := by
  constructor
  · intro τ v₀ r hτ hv0 hv1 hr
    exact free_plus_composition μW μA hm h0 h1 hPm hP0 hP1 hn hc hf hτ hH hr
      (bernoulli_pos hv0 hv1) hW hA hR
  · intro τ v₀ r hτ hv0 hv1 hr
    exact free_minus_composition μW μA hm h0 h1 hPm hP0 hP1 hn hc hf hτ hH hr
      (bernoulli_pos hv0 hv1) hW hA hR

end Stages
end BstLean.Part203
