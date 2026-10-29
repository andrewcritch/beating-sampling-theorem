import BstLean.Part252Root
import BstLean.Part252PassEvent

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12225) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12225) c (rowSplit c wl ws),
    ((12225 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12225 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12225) c (rowSplit c wl ws),
    ((12225 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12225 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12225 - 1)))
    (rowSplit c wl ws).good a ∂muI 12225 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12225) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12225 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12225) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12225 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12225) c (rowSplit c wl ws),
    hellG2 12225 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12225 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part252
