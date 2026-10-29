import BstLean.Part293SchurSelected
import BstLean.Part293Ledger

/-! The selected Schur event pays one charge for the whole low band. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part289 BstLean.BlueprintLow

noncomputable def schurCharge_of_band {n : ℕ} (hn : 8000 ≤ n) :
    NetworkCharge (retDist (statedDesign2 n).toCentres) schurCharge where
  event := selectedSchurRetained n
  measurable := selectedSchurRetained_measurable n
  nonneg := by norm_num [schurCharge]
  complement := (selectedSchurRetained_charge hn).trans (by norm_num [schurCharge])

end BstLean.Part293

/-- info: 'BstLean.Part293.schurCharge_of_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.schurCharge_of_band
