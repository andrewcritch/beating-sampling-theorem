import BstLean.Part152GC

/-! Integrate conditional failures over the complete second-layer distribution. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Set

/-- A uniform section bound gives a product-event bound. -/
theorem product_charge {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set (α × β)} (hS : MeasurableSet S) {p : ℝ}
    (hp : ∀ x, ν.real {y | (x, y) ∈ S} ≤ p) :
    (μ.prod ν).real S ≤ p := by
  have he : (μ.prod ν).real S = ∫ x, ν.real {y | (x, y) ∈ S} ∂μ := by
    rw [measureReal_def, Measure.prod_apply hS, ← integral_toReal]
    · rfl
    · exact (measurable_measure_prodMk_left hS).aemeasurable
    · exact Filter.Eventually.of_forall fun x => measure_lt_top _ _
  rw [he]
  have hi : Integrable (fun x => ν.real {y | (x, y) ∈ S}) μ := by
    refine Integrable.of_bound
      ((measurable_measure_prodMk_left hS).ennreal_toReal.aestronglyMeasurable) 1 ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
      exact measureReal_le_one
  exact (integral_mono hi (integrable_const p) hp).trans_eq (by simp)

/-- Pay the first-layer complement once and retain both full conditional tails. -/
theorem grouped_conditional_charge {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set α} {D S A : Set (α × β)} (hE : MeasurableSet E)
    (hD : MeasurableSet D) (hS : MeasurableSet S) (hA : MeasurableSet A)
    {δ pD pA : ℝ} (hδ : μ.real Eᶜ ≤ δ) (hpD : 0 ≤ pD) (hpA : 0 ≤ pA)
    (hs : ∀ x ∈ E, ∀ y, (x, y) ∈ S)
    (hd : ∀ x ∈ E, ν.real {y | (x, y) ∉ D} ≤ pD)
    (ha : ∀ x ∈ E, ν.real {y | (x, y) ∉ A} ≤ pA) :
    (μ.prod ν).real ((D ∩ S) ∩ A)ᶜ ≤ δ + pD + pA := by
  let T : Set (α × β) := (E ×ˢ univ) ∩ ((D ∩ S) ∩ A)ᶜ
  have hT : MeasurableSet T := (hE.prod MeasurableSet.univ).inter
    ((hD.inter hS).inter hA).compl
  have ht : (μ.prod ν).real T ≤ pD + pA := by
    apply product_charge hT
    intro x
    by_cases hx : x ∈ E
    · have hsub : {y | (x, y) ∈ T} ⊆
          {y | (x, y) ∉ D} ∪ {y | (x, y) ∉ A} := by
        intro y hy
        by_contra h
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
        exact hy.2 ⟨⟨h.1, hs x hx y⟩, h.2⟩
      exact (measureReal_mono hsub (measure_ne_top _ _)).trans
        ((measureReal_union_le _ _).trans (add_le_add (hd x hx) (ha x hx)))
    · have he : {y | (x, y) ∈ T} = ∅ := by
        ext y
        simp [T, hx]
      rw [he, measureReal_empty]
      exact add_nonneg hpD hpA
  have hsub : ((D ∩ S) ∩ A)ᶜ ⊆ (Eᶜ ×ˢ univ) ∪ T := by
    intro z hz
    by_cases he : z.1 ∈ E
    · exact Or.inr ⟨⟨he, mem_univ _⟩, hz⟩
    · exact Or.inl ⟨he, mem_univ _⟩
  have hc : (μ.prod ν).real (Eᶜ ×ˢ univ) ≤ δ := by
    rw [measureReal_prod_prod]
    simpa using hδ
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans ((add_le_add hc ht).trans_eq (by ring)))

end BstLean.Part233
#print axioms BstLean.Part233.product_charge
#print axioms BstLean.Part233.grouped_conditional_charge
