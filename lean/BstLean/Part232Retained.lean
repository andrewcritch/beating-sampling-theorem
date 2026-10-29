import BstLean.Part232Integration

/-! Part 232: retained restrictions keep their original mass and complement payment. -/
namespace BstLean.Part232
open MeasureTheory Real Set

section Retained
variable {C X : Type*} [MeasurableSpace C] [MeasurableSpace X]

/-- A measurable retained restriction has mass at most one. -/
lemma retained_mass (μ : Measure C) [IsProbabilityMeasure μ] {E : Set C}
    (_hE : MeasurableSet E) : (μ.restrict E).real univ ≤ 1 := by
  rw [measureReal_restrict_apply MeasurableSet.univ]
  simp only [univ_inter]
  exact measureReal_le_one

/-- Rejoin retained and excluded data without normalizing the retained measure. -/
theorem retained_complement (μ : Measure C) (ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set C} (hE : MeasurableSet E) {F : Set (C × X)} (hF : MeasurableSet F)
    {B δ : ℝ} (hret : ((μ.restrict E).prod ν).real F ≤ B)
    (hcomp : μ.real Eᶜ ≤ δ) : (μ.prod ν).real F ≤ δ + B := by
  have heq : ((μ.restrict E).prod ν).real F =
      (μ.prod ν).real (F ∩ (E ×ˢ univ)) := by
    rw [Measure.restrict_prod_eq_prod_univ, measureReal_restrict_apply hF]
  have hsub : F ⊆ (Eᶜ ×ˢ univ) ∪ (F ∩ (E ×ˢ univ)) := by
    intro x hx
    by_cases he : x.1 ∈ E
    · exact Or.inr ⟨hx, he, mem_univ _⟩
    · exact Or.inl ⟨he, mem_univ _⟩
  have hb := (measureReal_mono (μ := μ.prod ν) hsub).trans (measureReal_union_le _ _)
  rw [BstLean.Part156.real_prod_left, ← heq] at hb
  exact hb.trans (add_le_add hcomp hret)

/-- The conditional draw complement integrates to one payment on retained data. -/
theorem retained_sampling (μ : Measure C) (ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {E : Set C}
    (hE : MeasurableSet E) {T : Set (C × X)} (hT : MeasurableSet T)
    {δs : ℝ} (hδs : 0 ≤ δs)
    (hsamp : ∀ c ∈ E, ν.real (Prod.mk c ⁻¹' Tᶜ) ≤ δs) :
    ((μ.restrict E).prod ν).real Tᶜ ≤ δs := by
  have hm : Measurable (fun c => ν.real (Prod.mk c ⁻¹' Tᶜ)) :=
    (measurable_measure_prodMk_left hT.compl).ennreal_toReal
  have hi : Integrable (fun c => ν.real (Prod.mk c ⁻¹' Tᶜ)) (μ.restrict E) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  rw [BstLean.Part157.real_prod_eq _ _ hT.compl]
  have hb : ∀ᵐ c ∂μ.restrict E,
      ν.real (Prod.mk c ⁻¹' Tᶜ) ≤ δs + 0 * (0 : ℝ) ^ 2 := by
    filter_upwards [ae_restrict_mem hE] with c hc
    simpa using hsamp c hc
  simpa using affine_integral (r := fun _ => (0 : ℝ)) (μ.restrict E)
    (retained_mass μ hE) hδs
    (le_refl (0 : ℝ)) (integrable_const (0 ^ 2 : ℝ)) hi hb
    (le_refl (∫ c, (0 : ℝ) ^ 2 ∂μ.restrict E))

/-- LM replaces the fixed World cutoff payment in the complete retained ledger. -/
theorem lm_retained_master (μ : Measure C) (ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set C} (hE : MeasurableSet E) (cover : RadiusCover)
    {r : C → ℝ} (hr : ∀ c, 0 ≤ r c)
    {F T : Set (C × X)} (hF : MeasurableSet F) (hT : MeasurableSet T)
    {g : ℕ → ℝ} {c₀ c₁ v δs δret : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hδs : 0 ≤ δs)
    (hi : IntegrableOn (fun c => r c ^ 2) E μ)
    (hv : ∫ c in E, r c ^ 2 ∂μ ≤ v)
    (hline : ∀ i < cover.K, g i ≤ c₀ + c₁ * cover.h i ^ 2)
    (hterminal : 1 ≤ c₀ + c₁ * cover.h cover.K ^ 2)
    (hcells : ∀ c ∈ E, ∀ i, i < cover.K → radiusCell cover.h i (r c) →
      ν.real (Prod.mk c ⁻¹' (F ∩ T)) ≤ g i)
    (hsamp : ∀ c ∈ E, ν.real (Prod.mk c ⁻¹' Tᶜ) ≤ δs)
    (hcomp : μ.real Eᶜ ≤ δret) :
    (μ.prod ν).real F ≤ δret + (c₀ + c₁ * v) + δs := by
  have hcellsAE : ∀ᵐ c ∂μ.restrict E, ∀ i, i < cover.K →
      radiusCell cover.h i (r c) → ν.real (Prod.mk c ⁻¹' (F ∩ T)) ≤ g i := by
    filter_upwards [ae_restrict_mem hE] with c hc
    exact hcells c hc
  have hret := lm_one_sampling_payment (μ.restrict E) ν (retained_mass μ hE)
    cover hr hF hT hc₀ hc₁ hi hv hline hterminal hcellsAE
    (retained_sampling μ ν hE hT hδs hsamp)
  have h := retained_complement μ ν hE hF hret hcomp
  linarith

end Retained
end BstLean.Part232
