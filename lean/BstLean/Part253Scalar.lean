import BstLean.Part253Cert10
import BstLean.Part253Cert16
import BstLean.Part253Cert22
import BstLean.Part253Cert28
import BstLean.Part253Cert34
import BstLean.Part253Cert40
import BstLean.Part253Cert46
import BstLean.Part253Cert52

/-! Exact rational cell data and certificates. -/
namespace BstLean.Part253
open Real Set

theorem neededScalar (j : Fin 43) : ScalarCertificate ⟨j.val + 10, by omega⟩ := by
  match j with
  | ⟨0, _⟩ => exact scalarCell10
  | ⟨1, _⟩ => exact scalarCell11
  | ⟨2, _⟩ => exact scalarCell12
  | ⟨3, _⟩ => exact scalarCell13
  | ⟨4, _⟩ => exact scalarCell14
  | ⟨5, _⟩ => exact scalarCell15
  | ⟨6, _⟩ => exact scalarCell16
  | ⟨7, _⟩ => exact scalarCell17
  | ⟨8, _⟩ => exact scalarCell18
  | ⟨9, _⟩ => exact scalarCell19
  | ⟨10, _⟩ => exact scalarCell20
  | ⟨11, _⟩ => exact scalarCell21
  | ⟨12, _⟩ => exact scalarCell22
  | ⟨13, _⟩ => exact scalarCell23
  | ⟨14, _⟩ => exact scalarCell24
  | ⟨15, _⟩ => exact scalarCell25
  | ⟨16, _⟩ => exact scalarCell26
  | ⟨17, _⟩ => exact scalarCell27
  | ⟨18, _⟩ => exact scalarCell28
  | ⟨19, _⟩ => exact scalarCell29
  | ⟨20, _⟩ => exact scalarCell30
  | ⟨21, _⟩ => exact scalarCell31
  | ⟨22, _⟩ => exact scalarCell32
  | ⟨23, _⟩ => exact scalarCell33
  | ⟨24, _⟩ => exact scalarCell34
  | ⟨25, _⟩ => exact scalarCell35
  | ⟨26, _⟩ => exact scalarCell36
  | ⟨27, _⟩ => exact scalarCell37
  | ⟨28, _⟩ => exact scalarCell38
  | ⟨29, _⟩ => exact scalarCell39
  | ⟨30, _⟩ => exact scalarCell40
  | ⟨31, _⟩ => exact scalarCell41
  | ⟨32, _⟩ => exact scalarCell42
  | ⟨33, _⟩ => exact scalarCell43
  | ⟨34, _⟩ => exact scalarCell44
  | ⟨35, _⟩ => exact scalarCell45
  | ⟨36, _⟩ => exact scalarCell46
  | ⟨37, _⟩ => exact scalarCell47
  | ⟨38, _⟩ => exact scalarCell48
  | ⟨39, _⟩ => exact scalarCell49
  | ⟨40, _⟩ => exact scalarCell50
  | ⟨41, _⟩ => exact scalarCell51
  | ⟨42, _⟩ => exact scalarCell52
  | ⟨k + 43, h⟩ => omega

theorem scalar_on_needed {i : Fin 60} (hi : needed i) : ScalarCertificate i := by
  let j : Fin 43 := ⟨i.val - 10, by have := hi.2; omega⟩
  have he : (⟨j.val + 10, by omega⟩ : Fin 60) = i := by
    apply Fin.ext
    dsimp [j]
    have := hi.1
    omega
  rw [← he]
  exact neededScalar j

end BstLean.Part253
