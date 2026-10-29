import BstLean.Part256Supply

namespace BstLean.Part256
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192 BstLean.Part196
open BstLean.Part160 (AgFam agentEv)
open BstLean.Part169 (paperDesignP)
open BstLean.Part249
open BstLean.Part255 (LocalCovarianceOn)
open BstLean.Part253 (needed retunedCentre centreGroup retunedCutoff massTable SourceEvents)

theorem row_classifier_from_events
    {event : Set (AgFam 12225)} {caps : Fin 60 → ℝ}
    (C : LocalCovarianceOn event BstLean.Part255.cell caps)
    (hscalar : ∀ i : Fin 60, needed i → 0 ≤ caps i ∧
      (caps i + retunedCentre (centreGroup i)) / retunedCutoff i + massTable i ≤ optionBAgentFrame)
    (W : WorldPackage (paperProgram 12225)
      (BstLean.Part243.rowWorldParameters BstLean.Part243.proposedHiddenCharge))
    (t : ℝ) {E : Set (Ret 12225)} (hevent : MeasurableSet event)
    (hpayment : (retDist (paperCentres 12225)).real
      (agentEv (paperDesignP 12225) event)ᶜ ≤ (1/4000 : ℝ))
    (hE : MeasurableSet E)
    (hcharge : (retDist (paperCentres 12225)).real
      (BstLean.Part159.Hof W.hidden ∩ Eᶜ) ≤ baseChargeAllowance)
    (hwindow : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ covarianceGood event) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ Icc BstLean.Part254.worldLower BstLean.Part254.worldUpper)
    (hsource : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ covarianceGood event) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius, SourceEvents c)
    (hroot : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ covarianceGood event) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot)) :
    99 / 100 ≤ ((mlpTriple 2 12225).prod (sampMeas (10 ^ 12) 12225)).real
      {x | successNet x.1 t (progOut (paperDesignP 12225) t aL (10 ^ 12) x.1 x.2)} := by
  apply BstLean.Part256.row_classifier_from_inputs
    (cell := BstLean.Part255.cell) (capTable := caps)
    W t hevent hpayment hE hcharge ?_ hroot
  intro c hc
  obtain ⟨i, hi, hm⟩ := BstLean.Part255.cells_cover (hwindow c hc)
  exact ⟨BstLean.Part256.frameInputs_from_events C hi hm (hsource c hc)
    (hscalar i hi).1 (hscalar i hi).2⟩

theorem row_classifier_selected
    (W : WorldPackage (paperProgram 12225)
      (BstLean.Part243.rowWorldParameters BstLean.Part243.proposedHiddenCharge))
    (t : ℝ) {E : Set (Ret 12225)}
    (hE : MeasurableSet E)
    (hcharge : (retDist (paperCentres 12225)).real
      (BstLean.Part159.Hof W.hidden ∩ Eᶜ) ≤ baseChargeAllowance)
    (hwindow : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ BstLean.Part255.selectedGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ Icc BstLean.Part254.worldLower BstLean.Part254.worldUpper)
    (hsource : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ BstLean.Part255.selectedGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius, SourceEvents c)
    (hroot : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ BstLean.Part255.selectedGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot)) :
    99 / 100 ≤ ((mlpTriple 2 12225).prod (sampMeas (10 ^ 12) 12225)).real
      {x | successNet x.1 t (progOut (paperDesignP 12225) t aL (10 ^ 12) x.1 x.2)} := by
  exact row_classifier_from_events BstLean.Part255.localCov
    (fun i hi => scalar_on_needed hi) W t
    (BstLean.Part255.selected_measurable _ _) BstLean.Part255.paper_selected_payment
    hE hcharge hwindow hsource hroot

end BstLean.Part256
