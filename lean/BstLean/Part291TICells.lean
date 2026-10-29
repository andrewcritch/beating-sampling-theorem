import BstLean.Part291TICellsBase
import BstLean.Part291TICellsBand0
import BstLean.Part291TICellsBand1
import BstLean.Part291TICellsBand2
import BstLean.Part291TICellsBand3
import BstLean.Part291TICellsBand4
import BstLean.Part291TICellsBand5
import BstLean.Part291TICellsBand6
import BstLean.Part291TICellsBand7
import BstLean.Part291TICellsBand8
import BstLean.Part291TICellsBand9

namespace BstLean.BlueprintLow
open Real Set BstLean.Part255

theorem lowTISupplyBand {n : ℕ} (hn : 8000 ≤ n) (j : Fin 160) :
    LowTISupply n (lowTIParameters j) (frameNoiseLower j) (frameNoiseUpper j) := by
  by_cases h : j.val < 16
  · exact lowTISupplyBand0 hn j ⟨by omega, h⟩
  by_cases h1 : j.val < 32
  · exact lowTISupplyBand1 hn j ⟨by omega, h1⟩
  by_cases h2 : j.val < 48
  · exact lowTISupplyBand2 hn j ⟨by omega, h2⟩
  by_cases h3 : j.val < 64
  · exact lowTISupplyBand3 hn j ⟨by omega, h3⟩
  by_cases h4 : j.val < 80
  · exact lowTISupplyBand4 hn j ⟨by omega, h4⟩
  by_cases h5 : j.val < 96
  · exact lowTISupplyBand5 hn j ⟨by omega, h5⟩
  by_cases h6 : j.val < 112
  · exact lowTISupplyBand6 hn j ⟨by omega, h6⟩
  by_cases h7 : j.val < 128
  · exact lowTISupplyBand7 hn j ⟨by omega, h7⟩
  by_cases h8 : j.val < 144
  · exact lowTISupplyBand8 hn j ⟨by omega, h8⟩
  by_cases h9 : j.val < 160
  · exact lowTISupplyBand9 hn j ⟨by omega, h9⟩
  · exact lowTISupplyBand9 hn j ⟨by omega, j.isLt⟩

end BstLean.BlueprintLow

