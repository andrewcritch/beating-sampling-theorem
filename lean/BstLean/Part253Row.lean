import BstLean.Part253Supply
import BstLean.Part253Bridge

/-! The numerical cells enter the dimension-12225 row. The narrow World window
and the remaining source certificates are explicit hypotheses. -/
namespace BstLean.Part253
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192 BstLean.Part196
open BstLean.Part169 (paperDesignP)
open BstLean.Part249

theorem frame_from_source (C : LocalCovariance cell capTable)
    {c : Ret 12225} {i : Fin 60} (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell i)
    (F : SourceInputs c i) (hc : c ∈ optionBGood (paperDesignP 12225))
    (v : Fin (mA 12225) → ℝ) :
    ∫ ξ, (∑ j, BstLean.Part134.eDir ((paperDesignP 12225).bA c.1 c.2.1.1)
      (BstLean.Part157.hStand (paperDesignP 12225) c ξ) j * v j) ^ 2
        ∂BstLean.Part29.stdGauss (Fin 12225) ≤
      optionBAgentFrame / 12225 * ∑ j, v j ^ 2 :=
  frame_from_inputs (frameInputs_from_source C hi hm F) hc v

/-- This theorem does not turn stored decimal proposals into source certificates. -/
theorem row_classifier_from_source
    (C : LocalCovariance cell capTable)
    (W : WorldPackage (paperProgram 12225)
      (BstLean.Part243.rowWorldParameters BstLean.Part243.proposedHiddenCharge))
    (t : ℝ) {E : Set (Ret 12225)} (hE : MeasurableSet E)
    (hcharge : (retDist (paperCentres 12225)).real
      (BstLean.Part159.Hof W.hidden ∩ Eᶜ) ≤ baseChargeAllowance)
    (hwindow : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ optionBGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ worldInterval)
    (hsource : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ optionBGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius, ∀ i : Fin 60, needed i →
      BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell i →
      Nonempty (SourceInputs c i))
    (hroot : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ optionBGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot)) :
    99 / 100 ≤ ((mlpTriple 2 12225).prod (sampMeas (10 ^ 12) 12225)).real
      {x | successNet x.1 t (progOut (paperDesignP 12225) t aL (10 ^ 12) x.1 x.2)} := by
  apply BstLean.Part253.row_classifier_from_inputs (cell := cell) (capTable := capTable)
    W t hE hcharge ?_ hroot
  intro c hc
  obtain ⟨i, hi, hm⟩ := needed_cells_cover (hwindow c hc)
  obtain ⟨F⟩ := hsource c hc i hi hm
  exact ⟨frameInputs_from_source C hi hm F⟩

end BstLean.Part253
