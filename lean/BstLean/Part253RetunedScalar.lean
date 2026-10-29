import BstLean.Part253RetunedCert10
import BstLean.Part253RetunedCert16
import BstLean.Part253RetunedCert22
import BstLean.Part253RetunedCert28
import BstLean.Part253RetunedCert34
import BstLean.Part253RetunedCert40
import BstLean.Part253RetunedCert46
import BstLean.Part253RetunedCert52

/-! The retuned frame certificates cover every needed cell. -/
namespace BstLean.Part253

theorem retunedNeeded (j : Fin 43) : RetunedDataCertificate ⟨j.val + 10, by omega⟩ := by
  match j with
  | ⟨0, _⟩ => exact retunedCell10
  | ⟨1, _⟩ => exact retunedCell11
  | ⟨2, _⟩ => exact retunedCell12
  | ⟨3, _⟩ => exact retunedCell13
  | ⟨4, _⟩ => exact retunedCell14
  | ⟨5, _⟩ => exact retunedCell15
  | ⟨6, _⟩ => exact retunedCell16
  | ⟨7, _⟩ => exact retunedCell17
  | ⟨8, _⟩ => exact retunedCell18
  | ⟨9, _⟩ => exact retunedCell19
  | ⟨10, _⟩ => exact retunedCell20
  | ⟨11, _⟩ => exact retunedCell21
  | ⟨12, _⟩ => exact retunedCell22
  | ⟨13, _⟩ => exact retunedCell23
  | ⟨14, _⟩ => exact retunedCell24
  | ⟨15, _⟩ => exact retunedCell25
  | ⟨16, _⟩ => exact retunedCell26
  | ⟨17, _⟩ => exact retunedCell27
  | ⟨18, _⟩ => exact retunedCell28
  | ⟨19, _⟩ => exact retunedCell29
  | ⟨20, _⟩ => exact retunedCell30
  | ⟨21, _⟩ => exact retunedCell31
  | ⟨22, _⟩ => exact retunedCell32
  | ⟨23, _⟩ => exact retunedCell33
  | ⟨24, _⟩ => exact retunedCell34
  | ⟨25, _⟩ => exact retunedCell35
  | ⟨26, _⟩ => exact retunedCell36
  | ⟨27, _⟩ => exact retunedCell37
  | ⟨28, _⟩ => exact retunedCell38
  | ⟨29, _⟩ => exact retunedCell39
  | ⟨30, _⟩ => exact retunedCell40
  | ⟨31, _⟩ => exact retunedCell41
  | ⟨32, _⟩ => exact retunedCell42
  | ⟨33, _⟩ => exact retunedCell43
  | ⟨34, _⟩ => exact retunedCell44
  | ⟨35, _⟩ => exact retunedCell45
  | ⟨36, _⟩ => exact retunedCell46
  | ⟨37, _⟩ => exact retunedCell47
  | ⟨38, _⟩ => exact retunedCell48
  | ⟨39, _⟩ => exact retunedCell49
  | ⟨40, _⟩ => exact retunedCell50
  | ⟨41, _⟩ => exact retunedCell51
  | ⟨42, _⟩ => exact retunedCell52
  | ⟨k + 43, h⟩ => omega

theorem retuned_on_needed {i : Fin 60} (hi : needed i) : RetunedDataCertificate i := by
  let j : Fin 43 := ⟨i.val - 10, by have := hi.2; omega⟩
  have he : (⟨j.val + 10, by omega⟩ : Fin 60) = i := by
    apply Fin.ext
    dsimp [j]
    have := hi.1
    omega
  rw [← he]
  exact retunedNeeded j

end BstLean.Part253
