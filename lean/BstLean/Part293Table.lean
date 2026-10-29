import BstLean.Part292TableSupply
import BstLean.Part293TableEventFields

/-! The paid table charge for the actual stated program. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169
open BstLean.Part289

noncomputable def tableCharge_of_band {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882) :
    NetworkCharge (retDist (statedDesign2 n).toCentres) tableCharge where
  event := BstLean.Part292.tableEvent n
  measurable := (BstLean.Part292.tableSupplyBand_stated hn hn').2.1
  nonneg := by norm_num [tableCharge]
  complement := (BstLean.Part292.tableSupplyBand_stated hn hn').2.2.trans
    (by norm_num [tableCharge])

end BstLean.Part293

/-- info: 'BstLean.Part293.tableCharge_of_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.tableCharge_of_band
