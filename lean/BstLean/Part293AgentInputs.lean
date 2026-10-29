import BstLean.Part291AgentCombined
import BstLean.Part293DesignAdapter

/-! Thin Agent supply assembled directly from the accepted node 39 components. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part188
open BstLean.BlueprintLow

structure AgentSupplyInputs {n : ℕ} (c : Ret n) : Prop where
  band : LowBand n
  world_ne : c.1.2 ≠ 0
  tau_pos : 0 < (paperDesignP n).tau0 c
  centre_pos : 0 < normSq (bR c)
  interfaces : WFInterfaces (paperDesignP n) c agentDirectionCap
    (agentEnergyMomentCap / n) agentParallelCap
  energy : centreEnergy (paperDesignP n) c ≤ agentEnergyCap
  latitude : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c)
  output_pos : 0 < normSq c.2.1.2
  output_bound : normSq c.2.1.2 ≤ 2 * eR c * lowMixtureChi n

noncomputable def AgentSupplyInputs.comparisons {n : ℕ} {c : Ret n}
    (S : AgentSupplyInputs c) :=
  agentComparisonFieldsBand S.band c S.world_ne S.tau_pos S.centre_pos
    S.interfaces S.energy S.latitude S.output_pos S.output_bound

noncomputable def AgentSupplyInputs.split {n : ℕ} {c : Ret n}
    (S : AgentSupplyInputs c) :=
  agentSplitPremisesBand S.band c
    (show 0 < centreEnergy (paperDesignP n) c from
      div_pos S.centre_pos (by exact_mod_cast (show 0 < n by have := S.band.1; omega)))
    S.output_bound

noncomputable def AgentSupplyInputs.conditional_norms {n : ℕ} {c : Ret n}
    (S : AgentSupplyInputs c) :=
  agentConditionalNormsBand S.band c S.world_ne S.tau_pos S.centre_pos
    S.interfaces S.energy S.latitude (lowMixtureChi_pos n).le S.output_bound

theorem agentInputs_of_events {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hw : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.472 : ℝ) 0.528)
    (hc : 0 < normSq c.1.2) (hτ : 0 < (paperDesignP n).tau0 c)
    (hC : c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c))
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c))
    (hO : c ∈ BstLean.Part252.outputCentreEvent (paperDesignP n).toCentres)
    (hP : c ∈ BstLean.Part252.positiveOutputEvent (paperDesignP n).toCentres) :
    AgentSupplyInputs c := by
  obtain ⟨hb, hI, hE, _⟩ := agentCentreFieldsBand hn hw hc hτ hC
  have hcne : c.1.2 ≠ 0 := by intro hz; simp [hz, normSq] at hc
  exact ⟨hn, hcne, hτ, hb, interfaces_stated2_to_paper hI, hE, hL, hP hb,
    outputCentre_normalized (by have := hn.1; omega) hO⟩

end BstLean.Part293

/-- info: 'BstLean.Part293.agentInputs_of_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.agentInputs_of_events
