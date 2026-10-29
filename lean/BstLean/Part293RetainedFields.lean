import BstLean.Part293ActualLedger

/-! Fields of the actual common retained event, before Agent and frame supply. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part161 BstLean.Part169
open BstLean.Part289 BstLean.BlueprintLow

structure ActualRetainedFields {n : ℕ} (c : Ret n) : Prop where
  world_good : c ∈ Hof (BstLean.Part290.worldHidden n) ∩
    (Ethm (statedDesign2 n).toCentres ∩ Ethp (statedDesign2 n).toCentres)
  theta : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
    Icc (0.472 : ℝ) 0.528
  worldcentre_pos : 0 < normSq c.1.2
  tau_pos : 0 < (paperDesignP n).tau0 c
  source_agent : c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c)
  latitude : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c)
  outputcentre : c ∈ BstLean.Part252.outputCentreEvent (paperDesignP n).toCentres
  positiveoutput : c ∈ BstLean.Part252.positiveOutputEvent (paperDesignP n).toCentres
  table : c ∈ BstLean.Part292.tableEvent n

theorem actualRetainedFields {n : ℕ} (hn : LowBand n)
    (S : NetworkCharge (retDist (statedDesign2 n).toCentres) schurCharge)
    {c : Ret n} (hc : c ∈ (actualLedger hn S).retained.event) :
    ActualRetainedFields c := by
  have W := worldSupplyBand hn.1 hn.2
  have hw := actualLedger_hidden hn S hc
  have ha : c ∈ Ethm (statedDesign2 n).toCentres ∩ Ethp (statedDesign2 n).toCentres :=
    hc.1.2.resolve_left (fun h => h hw)
  have hworld := And.intro hw ha
  have hwindow := window_of_supply hn.1 W c hworld
  have hguard := tableWorldGuard_of_supply hn.1 W c hworld
  have htheta : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (0.472 : ℝ) 0.528 := by
    convert W.noise_window c hworld using 1 <;> norm_num <;> rfl
  have htau : 0 < (paperDesignP n).tau0 c := hwindow.2.1
  have hsource : c ∈ (sourceCharge_of_band hn.1).event := hc.1.1.1.1.2
  have hC := sourceFields_of_band hn.1 hsource htau
  have hlat : c ∈ (latitudeCharge_of_band hn).event := hc.1.1.1.2
  have hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c) :=
    hlat.1.1 htau ⟨hguard.1, by convert hguard.2 using 1 <;> norm_num <;> rfl⟩
  have hcpos : 0 < normSq c.1.2 :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm fun h => hwindow.1 (normSq_eq_zero h))
  exact ⟨hworld, htheta, hcpos, htau, hC, hL, hlat.1.2, hlat.2, hc.2⟩

end BstLean.Part293

/-- info: 'BstLean.Part293.actualRetainedFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.actualRetainedFields
