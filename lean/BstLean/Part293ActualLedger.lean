import BstLean.Part293LatitudeEvents
import BstLean.Part293World
import BstLean.Part293Table

/-! The six paid actual network events on the low band. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part161 BstLean.Part169
open BstLean.Part289 BstLean.BlueprintLow

noncomputable def actualLedger {n : ℕ} (hn : LowBand n)
    (S : NetworkCharge (retDist (statedDesign2 n).toCentres) schurCharge) :
    EventLedger (retDist (statedDesign2 n).toCentres) where
  world := worldCharge_of_supply hn.1 (worldSupplyBand hn.1 hn.2)
  source := sourceCharge_of_band hn.1
  latitude := latitudeCharge_of_band hn
  schur := S
  angle := angleCharge_of_supply hn.1 (worldSupplyBand hn.1 hn.2)
  table := tableCharge_of_band hn.1 hn.2

theorem actualLedger_hidden {n : ℕ} (hn : LowBand n)
    (S : NetworkCharge (retDist (statedDesign2 n).toCentres) schurCharge) :
    (actualLedger hn S).retained.event ⊆ Hof (BstLean.Part290.worldHidden n) := by
  intro c hc
  exact hc.1.1.1.1.1

end BstLean.Part293

/-- info: 'BstLean.Part293.actualLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.actualLedger
