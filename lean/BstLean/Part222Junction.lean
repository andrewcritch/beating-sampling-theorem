import BstLean.Part222EnergyEvent
import BstLean.Part222Allowance
import BstLean.Part219Direction
import BstLean.Part188Parallel

/-! The direction, energy and parallel supplies use one computed centre and one input distribution. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part188 BstLean.Part215
open BstLean.Part160 (muStand)

/-- The sharp directional event and the new energy event supply the joint interface.
The parallel projection premise is the actual computed-centre projection. -/
theorem interfaces_on_events {n : ℕ} (hn : 195 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) {e xiF xiP η : ℝ} {δ : ℝ≥0∞}
    (he : 0 < e) (hxiF : 0 ≤ xiF) (hxiP : 0 ≤ xiP) (hδ : δ ≠ 0)
    (hq : 1-BstLean.Part150.thetaC c.1.2 (D.tau0 c) ∈ Set.Icc (0 : ℝ) (27/50))
    (hb : (n : ℝ)*e ≤ normSq (D.bA c.1 c.2.1.1))
    (hfull : normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)-
      D.bA c.1 c.2.1.1) ≤ xiF)
    (hparallel : |(∑ j, (muStand D c-D.bA c.1 c.2.1.1) j*D.bA c.1 c.2.1.1 j)/
      nrm (D.bA c.1 c.2.1.1)| ≤ √xiP)
    (herr : c.2.1.1 ∈ sharpErrorEvent c.1.2 (D.tau0 c))
    (hop : c.2.1.1 ∈ operatorEvent c.1.2 (D.tau0 c) η δ)
    (hen : c.2.1.1 ∈ energyEvent c.1.2 (D.tau0 c)) :
    WFInterfaces D c (BstLean.Part219.paperDirectionBudget c.1.2 (D.tau0 c) e xiF η δ)
      (energyAllowance n) xiP := by
  have hbpos : 0 < normSq (D.bA c.1 c.2.1.1) :=
    lt_of_lt_of_le (mul_pos (by exact_mod_cast (show 0 < n by omega)) he) hb
  exact ⟨BstLean.Part219.directionMoment_paper hn D c hτ he hxiF hδ hq hb hfull herr hop,
    energyMoment_on_event (by omega) D c hen,
    parallelCentre_of_projection (by omega) D c hxiP hbpos hparallel⟩

/-- Centre complements, direction complements and energy complements are each paid once. -/
theorem common_event_charge {n : ℕ} (hn : 322 ≤ n) (c : Fin n → ℝ)
    {τ η δ δC : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hδ : 0 < δ)
    (C : Set (BstLean.Part177.TH n)) (hC : (nuA n).real Cᶜ ≤ δC) :
    (nuA n).real (C ∩
      (sharpErrorEvent c τ ∩ operatorEvent c τ η (ENNReal.ofReal δ)) ∩ energyEvent c τ)ᶜ ≤
      δC+7/25000+δ+1/20000 := by
  have hd := BstLean.Part219.directional_events_charge hn c hτ hη hδ
  have he := energy_event_charge (by omega) c τ
  rw [Set.compl_inter, Set.compl_inter]
  have hu := (measureReal_union_le _ _).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add hC hd)) he)
  linarith

/-- The paper operator payment and energy payment together contribute 0.00038 with the error event. -/
theorem common_event_charge_paper {n : ℕ} (hn : 322 ≤ n) (c : Fin n → ℝ)
    {τ η δC : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η)
    (C : Set (BstLean.Part177.TH n)) (hC : (nuA n).real Cᶜ ≤ δC) :
    (nuA n).real (C ∩
      (sharpErrorEvent c τ ∩ operatorEvent c τ η (ENNReal.ofReal (1/20000))) ∩
      energyEvent c τ)ᶜ ≤ δC+19/50000 := by
  have h := common_event_charge hn c hτ hη (by norm_num : (0 : ℝ) < 1/20000) C hC
  convert h using 1 <;> ring

#print axioms interfaces_on_events
#print axioms common_event_charge
#print axioms common_event_charge_paper
end BstLean.Part222
