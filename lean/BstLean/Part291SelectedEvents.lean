import BstLean.Part291Band

/-! A deterministic first-cell selection pays one conditional event charge.
Closed-cell overlap does not require a union bound over the noise cover. -/
namespace BstLean.BlueprintLow
open MeasureTheory Set

def selectedCell {X : Type*} {k : ℕ} (cells : Fin k → Set X) (j : Fin k) : Set X :=
  cells j \ ⋃ i : {i : Fin k // i < j}, cells i.val

theorem selectedCell_measurable {X : Type*} [MeasurableSpace X] {k : ℕ}
    (cells : Fin k → Set X) (hm : ∀ j, MeasurableSet (cells j)) (j : Fin k) :
    MeasurableSet (selectedCell cells j) :=
  (hm j).diff (MeasurableSet.iUnion fun i => hm i.val)

theorem selectedCell_unique {X : Type*} {k : ℕ} (cells : Fin k → Set X) {x : X} {i j : Fin k}
    (hi : x ∈ selectedCell cells i) (hj : x ∈ selectedCell cells j) : i = j := by
  apply le_antisymm
  · by_contra h
    have hji : j < i := lt_of_not_ge h
    exact hi.2 (mem_iUnion.mpr ⟨⟨j,hji⟩,hj.1⟩)
  · by_contra h
    have hij : i < j := lt_of_not_ge h
    exact hj.2 (mem_iUnion.mpr ⟨⟨i,hij⟩,hi.1⟩)

theorem selectedCell_exists {X : Type*} {k : ℕ} (cells : Fin k → Set X) {x : X}
    (hx : ∃ j, x ∈ cells j) : ∃ j, x ∈ selectedCell cells j := by
  classical
  let S : Finset (Fin k) := Finset.univ.filter fun j => x ∈ cells j
  have hS : S.Nonempty := by obtain ⟨j,hj⟩ := hx; exact ⟨j,by simp [S,hj]⟩
  let j := S.min' hS
  have hj : j ∈ S := Finset.min'_mem S hS
  refine ⟨j, (Finset.mem_filter.mp hj).2, ?_⟩
  intro h
  obtain ⟨i,hi⟩ := mem_iUnion.mp h
  have hmem : i.val ∈ S := by simp [S,hi]
  have hle : j ≤ i.val := Finset.min'_le S i.val hmem
  exact (not_le_of_gt i.property) hle

def selectedEvent {X A : Type*} {k : ℕ} (cells : Fin k → Set X)
    (events : Fin k → Set (X × A)) : Set (X × A) :=
  ⋂ j, ((selectedCell cells j)ᶜ ×ˢ univ) ∪ events j

theorem selectedEvent_measurable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {k : ℕ} (cells : Fin k → Set X) (events : Fin k → Set (X × A))
    (hc : ∀ j, MeasurableSet (cells j)) (he : ∀ j, MeasurableSet (events j)) :
    MeasurableSet (selectedEvent cells events) :=
  MeasurableSet.iInter fun j =>
    (((selectedCell_measurable cells hc j).compl.prod MeasurableSet.univ).union (he j))

theorem selectedEvent_charge {X A : Type*} [MeasurableSpace A] {k : ℕ}
    (μ : Measure A) [IsFiniteMeasure μ] (cells : Fin k → Set X) (events : Fin k → Set (X × A))
    {x : X} (hx : ∃ j, x ∈ cells j) {ε : ℝ}
    (he : ∀ j, x ∈ cells j → μ.real {a | (x,a) ∉ events j} ≤ ε) :
    μ.real {a | (x,a) ∉ selectedEvent cells events} ≤ ε := by
  obtain ⟨j,hj⟩ := selectedCell_exists cells hx
  apply le_trans (measureReal_mono ?_) (he j hj.1)
  intro a ha
  by_contra hevent
  apply ha
  apply mem_iInter.mpr
  intro i
  by_cases hi : x ∈ selectedCell cells i
  · have hji := selectedCell_unique cells hj hi
    subst i
    exact Or.inr (not_not.mp hevent)
  · exact Or.inl ⟨hi,mem_univ _⟩

end BstLean.BlueprintLow
