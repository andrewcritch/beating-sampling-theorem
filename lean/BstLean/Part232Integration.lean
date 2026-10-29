import BstLean.Part232Cells
import BstLean.Part157Hell

/-! Part 232: LM integration uses finite retained measures without normalization. -/
namespace BstLean.Part232
open MeasureTheory Real Set

section Integration
variable {C X : Type*} [MeasurableSpace C] [MeasurableSpace X]

/-- Integrate an affine squared-radius bound on a measure of mass at most one. -/
theorem affine_integral (μ : Measure C) [IsFiniteMeasure μ]
    (hmass : μ.real univ ≤ 1) {r f : C → ℝ} {c₀ c₁ v : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hi : Integrable (fun c => r c ^ 2) μ)
    (hf : Integrable f μ) (hbound : ∀ᵐ c ∂μ, f c ≤ c₀ + c₁ * r c ^ 2)
    (hv : ∫ c, r c ^ 2 ∂μ ≤ v) : ∫ c, f c ∂μ ≤ c₀ + c₁ * v := by
  calc
    ∫ c, f c ∂μ ≤ ∫ c, (c₀ + c₁ * r c ^ 2) ∂μ :=
      integral_mono_ae hf ((integrable_const c₀).add (hi.const_mul c₁)) hbound
    _ = c₀ * μ.real univ + c₁ * ∫ c, r c ^ 2 ∂μ := by
      rw [integral_add (integrable_const c₀) (hi.const_mul c₁), integral_const,
        integral_const_mul]
      simp [smul_eq_mul, mul_comm]
    _ ≤ c₀ + c₁ * v := by
      have h0 := mul_le_mul_of_nonneg_left hmass hc₀
      have h1 := mul_le_mul_of_nonneg_left hv hc₁
      linarith

/-- LM integrates conditional failure directly; it adds no charge for a cell cover. -/
theorem lm_integrated (μ : Measure C) (ν : Measure X)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hmass : μ.real univ ≤ 1)
    (cover : RadiusCover) {r : C → ℝ} (hr : ∀ c, 0 ≤ r c)
    {F : Set (C × X)} (hF : MeasurableSet F) {g : ℕ → ℝ} {c₀ c₁ v : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hi : Integrable (fun c => r c ^ 2) μ) (hv : ∫ c, r c ^ 2 ∂μ ≤ v)
    (hline : ∀ i < cover.K, g i ≤ c₀ + c₁ * cover.h i ^ 2)
    (hterminal : 1 ≤ c₀ + c₁ * cover.h cover.K ^ 2)
    (hcells : ∀ᵐ c ∂μ, ∀ i, i < cover.K → radiusCell cover.h i (r c) →
      ν.real (Prod.mk c ⁻¹' F) ≤ g i) :
    (μ.prod ν).real F ≤ c₀ + c₁ * v := by
  have hmeas : Measurable (fun c => ν.real (Prod.mk c ⁻¹' F)) :=
    (measurable_measure_prodMk_left hF).ennreal_toReal
  have hfi : Integrable (fun c => ν.real (Prod.mk c ⁻¹' F)) μ :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  rw [BstLean.Part157.real_prod_eq μ ν hF]
  apply affine_integral μ hmass hc₀ hc₁ hi hfi _ hv
  filter_upwards [hcells] with c hcellB
  rcases radius_cover cover.positive (hr c) with ⟨i, hi, hcell⟩ | htail
  · exact (hcellB i hi hcell).trans ((hline i hi).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (cover.lower_square hi (hr c) hcell) hc₁)))
  · exact (measureReal_le_one (μ := ν)).trans (hterminal.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (cover.nonneg le_rfl) htail.le 2) hc₁)))

/-- Separate sampling failure after LM integration, with one sampling payment. -/
theorem lm_one_sampling_payment (μ : Measure C) (ν : Measure X)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hmass : μ.real univ ≤ 1)
    (cover : RadiusCover) {r : C → ℝ} (hr : ∀ c, 0 ≤ r c)
    {F T : Set (C × X)} (hF : MeasurableSet F) (hT : MeasurableSet T)
    {g : ℕ → ℝ} {c₀ c₁ v δs : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hi : Integrable (fun c => r c ^ 2) μ) (hv : ∫ c, r c ^ 2 ∂μ ≤ v)
    (hline : ∀ i < cover.K, g i ≤ c₀ + c₁ * cover.h i ^ 2)
    (hterminal : 1 ≤ c₀ + c₁ * cover.h cover.K ^ 2)
    (hcells : ∀ᵐ c ∂μ, ∀ i, i < cover.K → radiusCell cover.h i (r c) →
      ν.real (Prod.mk c ⁻¹' (F ∩ T)) ≤ g i)
    (hsamp : (μ.prod ν).real Tᶜ ≤ δs) :
    (μ.prod ν).real F ≤ c₀ + c₁ * v + δs := by
  have hsub : F ⊆ (F ∩ T) ∪ Tᶜ := by
    intro x hx
    by_cases ht : x ∈ T
    · exact Or.inl ⟨hx, ht⟩
    · exact Or.inr ht
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (lm_integrated μ ν hmass cover hr (hF.inter hT) hc₀ hc₁
      hi hv hline hterminal hcells) hsamp))

end Integration
end BstLean.Part232
