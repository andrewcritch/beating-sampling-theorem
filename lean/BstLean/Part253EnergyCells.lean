import BstLean.Part253EnergyCert10
import BstLean.Part253EnergyCert16
import BstLean.Part253EnergyCert22
import BstLean.Part253EnergyCert28
import BstLean.Part253EnergyCert34
import BstLean.Part253EnergyCert40
import BstLean.Part253EnergyCert46
import BstLean.Part253EnergyCert52

/-! Every needed cell has its local upper computed-centre energy certificate. -/
namespace BstLean.Part253
open Real BstLean.Part211 BstLean.Part206

theorem upperEnergyNeeded (j : Fin 43) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode (j.val + 10)) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy ⟨j.val + 10, by omega⟩ := by
  match j with
  | ⟨0, _⟩ => exact upperEnergyCell10 hq0 hq
  | ⟨1, _⟩ => exact upperEnergyCell11 hq0 hq
  | ⟨2, _⟩ => exact upperEnergyCell12 hq0 hq
  | ⟨3, _⟩ => exact upperEnergyCell13 hq0 hq
  | ⟨4, _⟩ => exact upperEnergyCell14 hq0 hq
  | ⟨5, _⟩ => exact upperEnergyCell15 hq0 hq
  | ⟨6, _⟩ => exact upperEnergyCell16 hq0 hq
  | ⟨7, _⟩ => exact upperEnergyCell17 hq0 hq
  | ⟨8, _⟩ => exact upperEnergyCell18 hq0 hq
  | ⟨9, _⟩ => exact upperEnergyCell19 hq0 hq
  | ⟨10, _⟩ => exact upperEnergyCell20 hq0 hq
  | ⟨11, _⟩ => exact upperEnergyCell21 hq0 hq
  | ⟨12, _⟩ => exact upperEnergyCell22 hq0 hq
  | ⟨13, _⟩ => exact upperEnergyCell23 hq0 hq
  | ⟨14, _⟩ => exact upperEnergyCell24 hq0 hq
  | ⟨15, _⟩ => exact upperEnergyCell25 hq0 hq
  | ⟨16, _⟩ => exact upperEnergyCell26 hq0 hq
  | ⟨17, _⟩ => exact upperEnergyCell27 hq0 hq
  | ⟨18, _⟩ => exact upperEnergyCell28 hq0 hq
  | ⟨19, _⟩ => exact upperEnergyCell29 hq0 hq
  | ⟨20, _⟩ => exact upperEnergyCell30 hq0 hq
  | ⟨21, _⟩ => exact upperEnergyCell31 hq0 hq
  | ⟨22, _⟩ => exact upperEnergyCell32 hq0 hq
  | ⟨23, _⟩ => exact upperEnergyCell33 hq0 hq
  | ⟨24, _⟩ => exact upperEnergyCell34 hq0 hq
  | ⟨25, _⟩ => exact upperEnergyCell35 hq0 hq
  | ⟨26, _⟩ => exact upperEnergyCell36 hq0 hq
  | ⟨27, _⟩ => exact upperEnergyCell37 hq0 hq
  | ⟨28, _⟩ => exact upperEnergyCell38 hq0 hq
  | ⟨29, _⟩ => exact upperEnergyCell39 hq0 hq
  | ⟨30, _⟩ => exact upperEnergyCell40 hq0 hq
  | ⟨31, _⟩ => exact upperEnergyCell41 hq0 hq
  | ⟨32, _⟩ => exact upperEnergyCell42 hq0 hq
  | ⟨33, _⟩ => exact upperEnergyCell43 hq0 hq
  | ⟨34, _⟩ => exact upperEnergyCell44 hq0 hq
  | ⟨35, _⟩ => exact upperEnergyCell45 hq0 hq
  | ⟨36, _⟩ => exact upperEnergyCell46 hq0 hq
  | ⟨37, _⟩ => exact upperEnergyCell47 hq0 hq
  | ⟨38, _⟩ => exact upperEnergyCell48 hq0 hq
  | ⟨39, _⟩ => exact upperEnergyCell49 hq0 hq
  | ⟨40, _⟩ => exact upperEnergyCell50 hq0 hq
  | ⟨41, _⟩ => exact upperEnergyCell51 hq0 hq
  | ⟨42, _⟩ => exact upperEnergyCell52 hq0 hq
  | ⟨k + 43, h⟩ => omega

theorem upper_energy_on_needed {i : Fin 60} (hi : needed i) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 - noiseNode i.val) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy i := by
  let j : Fin 43 := ⟨i.val - 10, by have := hi.2; omega⟩
  have hv : j.val + 10 = i.val := by dsimp [j]; have := hi.1; omega
  have he : (⟨j.val + 10, by omega⟩ : Fin 60) = i := Fin.ext hv
  have h := upperEnergyNeeded j hq0 (by simpa only [hv] using hq)
  simpa only [he] using h

end BstLean.Part253
