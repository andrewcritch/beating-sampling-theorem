import BstLean.Part255Interface
import BstLean.Part256Cert10
import BstLean.Part256Cert16
import BstLean.Part256Cert22
import BstLean.Part256Cert28
import BstLean.Part256Cert34
import BstLean.Part256Cert40
import BstLean.Part256Cert46
import BstLean.Part256Cert52

namespace BstLean.Part256
open BstLean.Part253

theorem scalarNeeded (j : Fin 43) :
    0 ≤ BstLean.Part255.localCapTable (BstLean.Part255.sourceIndex j) ∧
    (BstLean.Part255.localCapTable (BstLean.Part255.sourceIndex j) +
      retunedCentre (centreGroup (BstLean.Part255.sourceIndex j))) /
      retunedCutoff (BstLean.Part255.sourceIndex j) +
      massTable (BstLean.Part255.sourceIndex j) ≤ BstLean.Part249.optionBAgentFrame := by
  constructor
  · rw [BstLean.Part255.localCapTable_source]
    exact (BstLean.Part255.grid j).2.2
  · match j with
    | ⟨0, _⟩ =>
      have h := margin10.1
      change (BstLean.Part255.localCapTable (10 : Fin 60) +
        retunedCentre (centreGroup 10)) / retunedCutoff 10 + massTable 10 ≤ _
      linarith
    | ⟨1, _⟩ =>
      have h := margin11.1
      change (BstLean.Part255.localCapTable (11 : Fin 60) +
        retunedCentre (centreGroup 11)) / retunedCutoff 11 + massTable 11 ≤ _
      linarith
    | ⟨2, _⟩ =>
      have h := margin12.1
      change (BstLean.Part255.localCapTable (12 : Fin 60) +
        retunedCentre (centreGroup 12)) / retunedCutoff 12 + massTable 12 ≤ _
      linarith
    | ⟨3, _⟩ =>
      have h := margin13.1
      change (BstLean.Part255.localCapTable (13 : Fin 60) +
        retunedCentre (centreGroup 13)) / retunedCutoff 13 + massTable 13 ≤ _
      linarith
    | ⟨4, _⟩ =>
      have h := margin14.1
      change (BstLean.Part255.localCapTable (14 : Fin 60) +
        retunedCentre (centreGroup 14)) / retunedCutoff 14 + massTable 14 ≤ _
      linarith
    | ⟨5, _⟩ =>
      have h := margin15.1
      change (BstLean.Part255.localCapTable (15 : Fin 60) +
        retunedCentre (centreGroup 15)) / retunedCutoff 15 + massTable 15 ≤ _
      linarith
    | ⟨6, _⟩ =>
      have h := margin16.1
      change (BstLean.Part255.localCapTable (16 : Fin 60) +
        retunedCentre (centreGroup 16)) / retunedCutoff 16 + massTable 16 ≤ _
      linarith
    | ⟨7, _⟩ =>
      have h := margin17.1
      change (BstLean.Part255.localCapTable (17 : Fin 60) +
        retunedCentre (centreGroup 17)) / retunedCutoff 17 + massTable 17 ≤ _
      linarith
    | ⟨8, _⟩ =>
      have h := margin18.1
      change (BstLean.Part255.localCapTable (18 : Fin 60) +
        retunedCentre (centreGroup 18)) / retunedCutoff 18 + massTable 18 ≤ _
      linarith
    | ⟨9, _⟩ =>
      have h := margin19.1
      change (BstLean.Part255.localCapTable (19 : Fin 60) +
        retunedCentre (centreGroup 19)) / retunedCutoff 19 + massTable 19 ≤ _
      linarith
    | ⟨10, _⟩ =>
      have h := margin20.1
      change (BstLean.Part255.localCapTable (20 : Fin 60) +
        retunedCentre (centreGroup 20)) / retunedCutoff 20 + massTable 20 ≤ _
      linarith
    | ⟨11, _⟩ =>
      have h := margin21.1
      change (BstLean.Part255.localCapTable (21 : Fin 60) +
        retunedCentre (centreGroup 21)) / retunedCutoff 21 + massTable 21 ≤ _
      linarith
    | ⟨12, _⟩ =>
      have h := margin22.1
      change (BstLean.Part255.localCapTable (22 : Fin 60) +
        retunedCentre (centreGroup 22)) / retunedCutoff 22 + massTable 22 ≤ _
      linarith
    | ⟨13, _⟩ =>
      have h := margin23.1
      change (BstLean.Part255.localCapTable (23 : Fin 60) +
        retunedCentre (centreGroup 23)) / retunedCutoff 23 + massTable 23 ≤ _
      linarith
    | ⟨14, _⟩ =>
      have h := margin24.1
      change (BstLean.Part255.localCapTable (24 : Fin 60) +
        retunedCentre (centreGroup 24)) / retunedCutoff 24 + massTable 24 ≤ _
      linarith
    | ⟨15, _⟩ =>
      have h := margin25.1
      change (BstLean.Part255.localCapTable (25 : Fin 60) +
        retunedCentre (centreGroup 25)) / retunedCutoff 25 + massTable 25 ≤ _
      linarith
    | ⟨16, _⟩ =>
      have h := margin26.1
      change (BstLean.Part255.localCapTable (26 : Fin 60) +
        retunedCentre (centreGroup 26)) / retunedCutoff 26 + massTable 26 ≤ _
      linarith
    | ⟨17, _⟩ =>
      have h := margin27.1
      change (BstLean.Part255.localCapTable (27 : Fin 60) +
        retunedCentre (centreGroup 27)) / retunedCutoff 27 + massTable 27 ≤ _
      linarith
    | ⟨18, _⟩ =>
      have h := margin28.1
      change (BstLean.Part255.localCapTable (28 : Fin 60) +
        retunedCentre (centreGroup 28)) / retunedCutoff 28 + massTable 28 ≤ _
      linarith
    | ⟨19, _⟩ =>
      have h := margin29.1
      change (BstLean.Part255.localCapTable (29 : Fin 60) +
        retunedCentre (centreGroup 29)) / retunedCutoff 29 + massTable 29 ≤ _
      linarith
    | ⟨20, _⟩ =>
      have h := margin30.1
      change (BstLean.Part255.localCapTable (30 : Fin 60) +
        retunedCentre (centreGroup 30)) / retunedCutoff 30 + massTable 30 ≤ _
      linarith
    | ⟨21, _⟩ =>
      have h := margin31.1
      change (BstLean.Part255.localCapTable (31 : Fin 60) +
        retunedCentre (centreGroup 31)) / retunedCutoff 31 + massTable 31 ≤ _
      linarith
    | ⟨22, _⟩ =>
      have h := margin32.1
      change (BstLean.Part255.localCapTable (32 : Fin 60) +
        retunedCentre (centreGroup 32)) / retunedCutoff 32 + massTable 32 ≤ _
      linarith
    | ⟨23, _⟩ =>
      have h := margin33.1
      change (BstLean.Part255.localCapTable (33 : Fin 60) +
        retunedCentre (centreGroup 33)) / retunedCutoff 33 + massTable 33 ≤ _
      linarith
    | ⟨24, _⟩ =>
      have h := margin34.1
      change (BstLean.Part255.localCapTable (34 : Fin 60) +
        retunedCentre (centreGroup 34)) / retunedCutoff 34 + massTable 34 ≤ _
      linarith
    | ⟨25, _⟩ =>
      have h := margin35.1
      change (BstLean.Part255.localCapTable (35 : Fin 60) +
        retunedCentre (centreGroup 35)) / retunedCutoff 35 + massTable 35 ≤ _
      linarith
    | ⟨26, _⟩ =>
      have h := margin36.1
      change (BstLean.Part255.localCapTable (36 : Fin 60) +
        retunedCentre (centreGroup 36)) / retunedCutoff 36 + massTable 36 ≤ _
      linarith
    | ⟨27, _⟩ =>
      have h := margin37.1
      change (BstLean.Part255.localCapTable (37 : Fin 60) +
        retunedCentre (centreGroup 37)) / retunedCutoff 37 + massTable 37 ≤ _
      linarith
    | ⟨28, _⟩ =>
      have h := margin38.1
      change (BstLean.Part255.localCapTable (38 : Fin 60) +
        retunedCentre (centreGroup 38)) / retunedCutoff 38 + massTable 38 ≤ _
      linarith
    | ⟨29, _⟩ =>
      have h := margin39.1
      change (BstLean.Part255.localCapTable (39 : Fin 60) +
        retunedCentre (centreGroup 39)) / retunedCutoff 39 + massTable 39 ≤ _
      linarith
    | ⟨30, _⟩ =>
      have h := margin40.1
      change (BstLean.Part255.localCapTable (40 : Fin 60) +
        retunedCentre (centreGroup 40)) / retunedCutoff 40 + massTable 40 ≤ _
      linarith
    | ⟨31, _⟩ =>
      have h := margin41.1
      change (BstLean.Part255.localCapTable (41 : Fin 60) +
        retunedCentre (centreGroup 41)) / retunedCutoff 41 + massTable 41 ≤ _
      linarith
    | ⟨32, _⟩ =>
      have h := margin42.1
      change (BstLean.Part255.localCapTable (42 : Fin 60) +
        retunedCentre (centreGroup 42)) / retunedCutoff 42 + massTable 42 ≤ _
      linarith
    | ⟨33, _⟩ =>
      have h := margin43.1
      change (BstLean.Part255.localCapTable (43 : Fin 60) +
        retunedCentre (centreGroup 43)) / retunedCutoff 43 + massTable 43 ≤ _
      linarith
    | ⟨34, _⟩ =>
      have h := margin44.1
      change (BstLean.Part255.localCapTable (44 : Fin 60) +
        retunedCentre (centreGroup 44)) / retunedCutoff 44 + massTable 44 ≤ _
      linarith
    | ⟨35, _⟩ =>
      have h := margin45.1
      change (BstLean.Part255.localCapTable (45 : Fin 60) +
        retunedCentre (centreGroup 45)) / retunedCutoff 45 + massTable 45 ≤ _
      linarith
    | ⟨36, _⟩ =>
      have h := margin46.1
      change (BstLean.Part255.localCapTable (46 : Fin 60) +
        retunedCentre (centreGroup 46)) / retunedCutoff 46 + massTable 46 ≤ _
      linarith
    | ⟨37, _⟩ =>
      have h := margin47.1
      change (BstLean.Part255.localCapTable (47 : Fin 60) +
        retunedCentre (centreGroup 47)) / retunedCutoff 47 + massTable 47 ≤ _
      linarith
    | ⟨38, _⟩ =>
      have h := margin48.1
      change (BstLean.Part255.localCapTable (48 : Fin 60) +
        retunedCentre (centreGroup 48)) / retunedCutoff 48 + massTable 48 ≤ _
      linarith
    | ⟨39, _⟩ =>
      have h := margin49.1
      change (BstLean.Part255.localCapTable (49 : Fin 60) +
        retunedCentre (centreGroup 49)) / retunedCutoff 49 + massTable 49 ≤ _
      linarith
    | ⟨40, _⟩ =>
      have h := margin50.1
      change (BstLean.Part255.localCapTable (50 : Fin 60) +
        retunedCentre (centreGroup 50)) / retunedCutoff 50 + massTable 50 ≤ _
      linarith
    | ⟨41, _⟩ =>
      have h := margin51.1
      change (BstLean.Part255.localCapTable (51 : Fin 60) +
        retunedCentre (centreGroup 51)) / retunedCutoff 51 + massTable 51 ≤ _
      linarith
    | ⟨42, _⟩ =>
      have h := margin52.1
      change (BstLean.Part255.localCapTable (52 : Fin 60) +
        retunedCentre (centreGroup 52)) / retunedCutoff 52 + massTable 52 ≤ _
      linarith
    | ⟨k+43,h⟩ => omega

theorem scalar_on_needed {i : Fin 60} (hi : needed i) :
    0 ≤ BstLean.Part255.localCapTable i ∧
    (BstLean.Part255.localCapTable i + retunedCentre (centreGroup i)) /
      retunedCutoff i + massTable i ≤ BstLean.Part249.optionBAgentFrame := by
  obtain ⟨j,rfl⟩ := BstLean.Part255.needed_has_index i hi
  exact scalarNeeded j

end BstLean.Part256
