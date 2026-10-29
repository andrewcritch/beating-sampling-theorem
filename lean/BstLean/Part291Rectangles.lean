import BstLean.Part291Rectangles0
import BstLean.Part291Rectangles1
import BstLean.Part291Rectangles2
import BstLean.Part291Rectangles3
import BstLean.Part291Rectangles4
import BstLean.Part291Rectangles5
namespace BstLean.BlueprintLow
noncomputable def lowRectangleBand (i : Fin 6) (j : Fin 160) :
    FrameRectangleCertificate (frameDimLower i) (frameDimUpper i)
      (frameNoiseLower j) (frameNoiseUpper j) (lowTIParameters j) := by
  match i with
  | ⟨0,_⟩ => exact lowRectangles0 j
  | ⟨1,_⟩ => exact lowRectangles1 j
  | ⟨2,_⟩ => exact lowRectangles2 j
  | ⟨3,_⟩ => exact lowRectangles3 j
  | ⟨4,_⟩ => exact lowRectangles4 j
  | ⟨5,_⟩ => exact lowRectangles5 j
  | ⟨i+6,h⟩ => exact False.elim (by omega)
end BstLean.BlueprintLow
