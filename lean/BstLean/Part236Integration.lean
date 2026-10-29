import BstLean.Part236Scalar
import BstLean.Part232Retained

/-! RF integrates marginal payments on unnormalized retained measures. -/
namespace BstLean.Part236
open MeasureTheory Real Set

section
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- RF integrates three marginal moments on the original retained measure. -/
theorem rf_integral (μ : Measure Ω) [IsFiniteMeasure μ]
    (hmass : μ.real univ ≤ 1) {ρ x y F : Ω → ℝ} {c₀ c₁ q r v A B : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (iρ : Integrable (fun ω => ρ ω ^ 2) μ)
    (ix : Integrable (fun ω => x ω ^ 2) μ) (iy : Integrable y μ) (iF : Integrable F μ)
    (hF : ∀ᵐ ω ∂μ, F ω ≤ c₀ + c₁ * ρ ω ^ 2 + q * x ω ^ 2 + r * y ω)
    (hv : ∫ ω, ρ ω ^ 2 ∂μ ≤ v) (hA : ∫ ω, x ω ^ 2 ∂μ ≤ A)
    (hB : ∫ ω, y ω ∂μ ≤ B) :
    ∫ ω, F ω ∂μ ≤ c₀ + c₁ * v + q * A + r * B := by
  have i0 : Integrable (fun ω => c₀ + c₁ * ρ ω ^ 2) μ :=
    (integrable_const c₀).add (iρ.const_mul c₁)
  have i1 : Integrable (fun ω => c₀ + c₁ * ρ ω ^ 2 + q * x ω ^ 2) μ :=
    i0.add (ix.const_mul q)
  calc
    ∫ ω, F ω ∂μ ≤ ∫ ω, (c₀ + c₁ * ρ ω ^ 2 + q * x ω ^ 2 + r * y ω) ∂μ :=
      integral_mono_ae iF (i1.add (iy.const_mul r)) hF
    _ = c₀ * μ.real univ + c₁ * ∫ ω, ρ ω ^ 2 ∂μ +
        q * ∫ ω, x ω ^ 2 ∂μ + r * ∫ ω, y ω ∂μ := by
      rw [integral_add i1 (iy.const_mul r), integral_add i0 (ix.const_mul q),
        integral_add (integrable_const c₀) (iρ.const_mul c₁), integral_const]
      simp only [integral_const_mul, smul_eq_mul, mul_comm (μ.real univ) c₀]
    _ ≤ c₀ + c₁ * v + q * A + r * B := by
      have h0 := mul_le_mul_of_nonneg_left hmass hc₀
      have h1 := mul_le_mul_of_nonneg_left hv hc₁
      have h2 := mul_le_mul_of_nonneg_left hA hq
      have h3 := mul_le_mul_of_nonneg_left hB hr
      linarith

/-- The two-dimensional cover gives the RF payment without cell union payments. -/
theorem rf_product_integrated (μ : Measure Ω) (ν : Measure X)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hmass : μ.real univ ≤ 1)
    (R : BstLean.Part232.RadiusCover) (C : FrameCover)
    {ρ x y : Ω → ℝ} {F : Set (Ω × X)} (hF : MeasurableSet F)
    {c₀ c₁ q r v A B : ℝ} {g : ℕ → ℕ → ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hq : 0 < q) (hr : 0 ≤ r)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hx : ∀ ω, 0 ≤ x ω) (hy : ∀ ω, 0 ≤ y ω)
    (hmax : ∀ᵐ ω ∂μ, x ω + y ω ≤ C.maximum)
    (iρ : Integrable (fun ω => ρ ω ^ 2) μ)
    (ix : Integrable (fun ω => x ω ^ 2) μ) (iy : Integrable y μ)
    (hv : ∫ ω, ρ ω ^ 2 ∂μ ≤ v) (hA : ∫ ω, x ω ^ 2 ∂μ ≤ A)
    (hB : ∫ ω, y ω ∂μ ≤ B)
    (hline : ∀ i < R.K, ∀ j < C.K,
      g i j ≤ c₀ + c₁ * R.h i ^ 2 + framePrice q r (C.h j))
    (hterminal : 1 ≤ c₀ + c₁ * R.h R.K ^ 2)
    (hcells : ∀ᵐ ω ∂μ, ∀ i < R.K, ∀ j < C.K,
      BstLean.Part232.radiusCell R.h i (ρ ω) →
      BstLean.Part232.radiusCell C.h j (x ω + y ω) →
      ν.real (Prod.mk ω ⁻¹' F) ≤ g i j) :
    (μ.prod ν).real F ≤ c₀ + c₁ * v + q * A + r * B := by
  have hm : Measurable (fun ω => ν.real (Prod.mk ω ⁻¹' F)) :=
    (measurable_measure_prodMk_left hF).ennreal_toReal
  have hi : Integrable (fun ω => ν.real (Prod.mk ω ⁻¹' F)) μ :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  rw [BstLean.Part157.real_prod_eq μ ν hF]
  apply rf_integral μ hmass hc₀ hc₁ hq.le hr iρ ix iy hi _ hv hA hB
  filter_upwards [hmax, hcells] with ω hmaxω hcellω
  exact product_majorant R C hq hr hc₁ (hx ω) (hy ω) (hρ ω) hmaxω hline
    hterminal hcellω (fun _ => measureReal_le_one)

/-- Sampling and retained complements have separate single payments. -/
theorem rf_retained_ledger (μ : Measure Ω) (ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set Ω} (hE : MeasurableSet E) {F T : Set (Ω × X)}
    (hF : MeasurableSet F) (hT : MeasurableSet T) {B δs δret : ℝ}
    (hB : ((μ.restrict E).prod ν).real (F ∩ T) ≤ B)
    (hs : ((μ.restrict E).prod ν).real Tᶜ ≤ δs)
    (hret : μ.real Eᶜ ≤ δret) : (μ.prod ν).real F ≤ δret + B + δs := by
  have hsub : F ⊆ (F ∩ T) ∪ Tᶜ := by
    intro ω hω
    by_cases ht : ω ∈ T
    · exact Or.inl ⟨hω, ht⟩
    · exact Or.inr ht
  have hb := (measureReal_mono (μ := (μ.restrict E).prod ν) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add hB hs))
  have h := BstLean.Part232.retained_complement μ ν hE hF hb hret
  linarith
end
end BstLean.Part236
