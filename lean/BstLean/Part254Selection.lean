import BstLean.Part249Covariance

/-! A finite, deterministic choice of covariance event retains one payment.
This construction does not identify the chosen event with Option B's event. -/
namespace BstLean.Part254
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nuA)

def selectedEvent {n N : ℕ} (select : ℝ → Fin N) (E : Fin N → Set (AgFam n)) :
    Set (AgFam n) := {k | k ∈ E (select (thetaC k.1.1 k.1.2))}

theorem selectedEvent_measurable {n N : ℕ} (select : ℝ → Fin N)
    (hselect : ∀ i, MeasurableSet {θ | select θ = i})
    (E : Fin N → Set (AgFam n)) (hE : ∀ i, MeasurableSet (E i)) :
    MeasurableSet (selectedEvent select E) := by
  have heq : selectedEvent select E =
      ⋃ i : Fin N, {k : AgFam n | select (thetaC k.1.1 k.1.2) = i} ∩ E i := by
    ext k
    simp only [selectedEvent, mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨i, hi, h⟩
      simpa only [hi] using h
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    ((hselect i).preimage measurable_thetaC_key').inter (hE i)

theorem selectedEvent_ret_charge {n N : ℕ} (D : Design n) (hτW : TauWorld D)
    (select : ℝ → Fin N) (hselect : ∀ i, MeasurableSet {θ | select θ = i})
    (E : Fin N → Set (AgFam n)) (hE : ∀ i, MeasurableSet (E i))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcharge : ∀ (c : Fin n → ℝ) (τ : ℝ), 0 < τ →
      (nuA n).real {a | ((c, τ), a) ∉ E (select (thetaC c τ))} ≤ ε) :
    (retDist D.toCentres).real (agentEv D (selectedEvent select E))ᶜ ≤ ε := by
  rw [agentEv_compl]
  exact retDist_agent_charge D hτW
    (selectedEvent_measurable select hselect E hE) hε hcharge

end BstLean.Part254
