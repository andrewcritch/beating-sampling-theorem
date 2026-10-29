import BstLean.Part269BlockSupplies0Cells0
import BstLean.Part269BlockSupplies0Cells1
namespace BstLean.Part269.BG0
open Real Set BstLean.Part263 BstLean.Part264 BstLean.Part264b BstLean.Part255
theorem supplies {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) (j : Fin 43) :
    Supply n (parameters j) (cellLower G (sourceIndex j)) (cellUpper G (sourceIndex j)) := by
  match j with
  | ⟨0,_⟩ => exact supply10 hn G ht
  | ⟨1,_⟩ => exact supply11 hn G ht
  | ⟨2,_⟩ => exact supply12 hn G ht
  | ⟨3,_⟩ => exact supply13 hn G ht
  | ⟨4,_⟩ => exact supply14 hn G ht
  | ⟨5,_⟩ => exact supply15 hn G ht
  | ⟨6,_⟩ => exact supply16 hn G ht
  | ⟨7,_⟩ => exact supply17 hn G ht
  | ⟨8,_⟩ => exact supply18 hn G ht
  | ⟨9,_⟩ => exact supply19 hn G ht
  | ⟨10,_⟩ => exact supply20 hn G ht
  | ⟨11,_⟩ => exact supply21 hn G ht
  | ⟨12,_⟩ => exact supply22 hn G ht
  | ⟨13,_⟩ => exact supply23 hn G ht
  | ⟨14,_⟩ => exact supply24 hn G ht
  | ⟨15,_⟩ => exact supply25 hn G ht
  | ⟨16,_⟩ => exact supply26 hn G ht
  | ⟨17,_⟩ => exact supply27 hn G ht
  | ⟨18,_⟩ => exact supply28 hn G ht
  | ⟨19,_⟩ => exact supply29 hn G ht
  | ⟨20,_⟩ => exact supply30 hn G ht
  | ⟨21,_⟩ => exact supply31 hn G ht
  | ⟨22,_⟩ => exact supply32 hn G ht
  | ⟨23,_⟩ => exact supply33 hn G ht
  | ⟨24,_⟩ => exact supply34 hn G ht
  | ⟨25,_⟩ => exact supply35 hn G ht
  | ⟨26,_⟩ => exact supply36 hn G ht
  | ⟨27,_⟩ => exact supply37 hn G ht
  | ⟨28,_⟩ => exact supply38 hn G ht
  | ⟨29,_⟩ => exact supply39 hn G ht
  | ⟨30,_⟩ => exact supply40 hn G ht
  | ⟨31,_⟩ => exact supply41 hn G ht
  | ⟨32,_⟩ => exact supply42 hn G ht
  | ⟨33,_⟩ => exact supply43 hn G ht
  | ⟨34,_⟩ => exact supply44 hn G ht
  | ⟨35,_⟩ => exact supply45 hn G ht
  | ⟨36,_⟩ => exact supply46 hn G ht
  | ⟨37,_⟩ => exact supply47 hn G ht
  | ⟨38,_⟩ => exact supply48 hn G ht
  | ⟨39,_⟩ => exact supply49 hn G ht
  | ⟨40,_⟩ => exact supply50 hn G ht
  | ⟨41,_⟩ => exact supply51 hn G ht
  | ⟨42,_⟩ => exact supply52 hn G ht
  | ⟨j+43,h⟩ => exact False.elim (by omega)

theorem radii {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex j)) :
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius := by
  match j with
  | ⟨0,_⟩ => exact (geometry10 hn G ht hθ).2.2
  | ⟨1,_⟩ => exact (geometry11 hn G ht hθ).2.2
  | ⟨2,_⟩ => exact (geometry12 hn G ht hθ).2.2
  | ⟨3,_⟩ => exact (geometry13 hn G ht hθ).2.2
  | ⟨4,_⟩ => exact (geometry14 hn G ht hθ).2.2
  | ⟨5,_⟩ => exact (geometry15 hn G ht hθ).2.2
  | ⟨6,_⟩ => exact (geometry16 hn G ht hθ).2.2
  | ⟨7,_⟩ => exact (geometry17 hn G ht hθ).2.2
  | ⟨8,_⟩ => exact (geometry18 hn G ht hθ).2.2
  | ⟨9,_⟩ => exact (geometry19 hn G ht hθ).2.2
  | ⟨10,_⟩ => exact (geometry20 hn G ht hθ).2.2
  | ⟨11,_⟩ => exact (geometry21 hn G ht hθ).2.2
  | ⟨12,_⟩ => exact (geometry22 hn G ht hθ).2.2
  | ⟨13,_⟩ => exact (geometry23 hn G ht hθ).2.2
  | ⟨14,_⟩ => exact (geometry24 hn G ht hθ).2.2
  | ⟨15,_⟩ => exact (geometry25 hn G ht hθ).2.2
  | ⟨16,_⟩ => exact (geometry26 hn G ht hθ).2.2
  | ⟨17,_⟩ => exact (geometry27 hn G ht hθ).2.2
  | ⟨18,_⟩ => exact (geometry28 hn G ht hθ).2.2
  | ⟨19,_⟩ => exact (geometry29 hn G ht hθ).2.2
  | ⟨20,_⟩ => exact (geometry30 hn G ht hθ).2.2
  | ⟨21,_⟩ => exact (geometry31 hn G ht hθ).2.2
  | ⟨22,_⟩ => exact (geometry32 hn G ht hθ).2.2
  | ⟨23,_⟩ => exact (geometry33 hn G ht hθ).2.2
  | ⟨24,_⟩ => exact (geometry34 hn G ht hθ).2.2
  | ⟨25,_⟩ => exact (geometry35 hn G ht hθ).2.2
  | ⟨26,_⟩ => exact (geometry36 hn G ht hθ).2.2
  | ⟨27,_⟩ => exact (geometry37 hn G ht hθ).2.2
  | ⟨28,_⟩ => exact (geometry38 hn G ht hθ).2.2
  | ⟨29,_⟩ => exact (geometry39 hn G ht hθ).2.2
  | ⟨30,_⟩ => exact (geometry40 hn G ht hθ).2.2
  | ⟨31,_⟩ => exact (geometry41 hn G ht hθ).2.2
  | ⟨32,_⟩ => exact (geometry42 hn G ht hθ).2.2
  | ⟨33,_⟩ => exact (geometry43 hn G ht hθ).2.2
  | ⟨34,_⟩ => exact (geometry44 hn G ht hθ).2.2
  | ⟨35,_⟩ => exact (geometry45 hn G ht hθ).2.2
  | ⟨36,_⟩ => exact (geometry46 hn G ht hθ).2.2
  | ⟨37,_⟩ => exact (geometry47 hn G ht hθ).2.2
  | ⟨38,_⟩ => exact (geometry48 hn G ht hθ).2.2
  | ⟨39,_⟩ => exact (geometry49 hn G ht hθ).2.2
  | ⟨40,_⟩ => exact (geometry50 hn G ht hθ).2.2
  | ⟨41,_⟩ => exact (geometry51 hn G ht hθ).2.2
  | ⟨42,_⟩ => exact (geometry52 hn G ht hθ).2.2
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def covarianceInputs {n : ℕ} (hn : n ∈ Icc 12350 12374)
    (R : ScalarRow n) (ht : R.grid.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) (A : FrameRepair n R) :
    CovarianceInputs n R.grid parameters (caps A) :=
  covarianceInputs_from_supplies (by have := hn.1; omega) A (supplies hn R.grid ht)
    (fun j _ hθ => radii hn R.grid ht j hθ)
end BstLean.Part269.BG0
