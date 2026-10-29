import BstLean.Part212Event

/-! The fresh latitude charge transfers to the retained distribution once. -/
namespace BstLean.Part212
open MeasureTheory
open scoped ENNReal
open BstLean.Part157 BstLean.Part160

/-- Apply the fresh event only inside the retained World window. -/
def guardedLatitudeEvent (n : ℕ) (Γ : Set ((Fin n → ℝ) × ℝ)) (C : ℝ≥0∞) :
    Set (AgFam n) := {k | k.1 ∈ Γ → k ∈ latitudeEvent n C}

theorem measurableSet_guardedLatitudeEvent {n : ℕ}
    {Γ : Set ((Fin n → ℝ) × ℝ)} (hΓ : MeasurableSet Γ) (C : ℝ≥0∞) :
    MeasurableSet (guardedLatitudeEvent n Γ C) := by
  have he : guardedLatitudeEvent n Γ C =
      (Prod.fst ⁻¹' Γ)ᶜ ∪ latitudeEvent n C := by
    ext k
    simp only [guardedLatitudeEvent, Set.mem_setOf_eq, Set.mem_union,
      Set.mem_compl_iff, Set.mem_preimage]
    tauto
  rw [he]
  exact (hΓ.preimage measurable_fst).compl.union (measurableSet_latitudeEvent n C)

theorem guardedLatitudeEvent_charge {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    {Γ : Set ((Fin n → ℝ) × ℝ)} {C : ℝ≥0∞} {δ : ℝ} (hδ : 0 ≤ δ)
    (hcharge : (c, τ) ∈ Γ →
      (BstLean.Part153.nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n C} ≤ δ) :
    (BstLean.Part153.nuA n).real {θ | ((c, τ), θ) ∉ guardedLatitudeEvent n Γ C} ≤ δ := by
  by_cases hw : (c, τ) ∈ Γ
  · simpa only [guardedLatitudeEvent, Set.mem_setOf_eq, hw, true_implies] using hcharge hw
  · have he : {θ | ((c, τ), θ) ∉ guardedLatitudeEvent n Γ C} = ∅ := by
      ext θ
      simp [guardedLatitudeEvent, hw]
    rw [he, measureReal_empty]
    exact hδ

theorem latitudeEvent_retained_charge {n : ℕ} (D : Design n) (hτ : TauWorld D)
    {C : ℝ≥0∞} {δ : ℝ} (hδ : 0 ≤ δ)
    (hcharge : ∀ (c : Fin n → ℝ) (τ : ℝ), 0 < τ →
      (BstLean.Part153.nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n C} ≤ δ) :
    (retDist D.toCentres).real (agentEv D (latitudeEvent n C))ᶜ ≤ δ := by
  rw [agentEv_compl]
  exact retDist_agent_charge D hτ (measurableSet_latitudeEvent n C) hδ hcharge

/-- Integrate window-local supplies without another World payment. -/
theorem guardedLatitudeEvent_retained_charge {n : ℕ} (D : Design n) (hτ : TauWorld D)
    {Γ : Set ((Fin n → ℝ) × ℝ)} (hΓ : MeasurableSet Γ)
    {C : ℝ≥0∞} {δ : ℝ} (hδ : 0 ≤ δ)
    (hcharge : ∀ (c : Fin n → ℝ) (τ : ℝ), 0 < τ → (c, τ) ∈ Γ →
      (BstLean.Part153.nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n C} ≤ δ) :
    (retDist D.toCentres).real (agentEv D (guardedLatitudeEvent n Γ C))ᶜ ≤ δ := by
  rw [agentEv_compl]
  exact retDist_agent_charge D hτ (measurableSet_guardedLatitudeEvent hΓ C) hδ
    (fun c τ hτ => guardedLatitudeEvent_charge c τ hδ (hcharge c τ hτ))

/-- Preserve the existing retained-data payment and add the fresh payment once. -/
theorem base_latitude_charge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {Ebase Elat : Set Ω} {δbase δlat : ℝ}
    (hbase : μ.real Ebaseᶜ ≤ δbase) (hlat : μ.real Elatᶜ ≤ δlat) :
    μ.real (Ebase ∩ Elat)ᶜ ≤ δbase + δlat := by
  rw [Set.compl_inter]
  exact (measureReal_union_le _ _).trans (add_le_add hbase hlat)
end BstLean.Part212
