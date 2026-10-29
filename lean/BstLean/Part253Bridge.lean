import BstLean.Part253Local

/-! The local frame enters the existing dimension-12225 classifier junction. -/
namespace BstLean.Part253
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part188
open BstLean.Part199 BstLean.Part161 BstLean.Part182
open BstLean.Part169 (paperDesignP)
open BstLean.Part192 BstLean.Part196 BstLean.Part156

open BstLean.Part249

/-- The moment event and covariance event cost .0003 in total.
The base event excludes those two payments. -/
noncomputable def agentPackage {cell : Fin 60 → Set ℝ} {capTable : Fin 60 → ℝ}
    {H E : Set (Ret 12225)} (hE : MeasurableSet E)
    {radius frame root charge t : ℝ}
    (hcharge : (retDist (paperCentres 12225)).real (H ∩ Eᶜ) ≤ charge)
    (hframe : ∀ c ∈ goodSet H (E ∩ optionBGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) radius, Nonempty (LocalFrameInputs cell capTable c frame))
    (hroot : ∀ c ∈ goodSet H (E ∩ optionBGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) radius, Nonempty (BstLean.Part243.RootInputs 12225 t c root)) :
    BstLean.Part243.AgentPackage 12225 H radius frame root (charge + 3 / 10000) t := by
  have hTI := optionB_good_charge (by norm_num : 11883 ≤ 12225) (paperDesignP 12225)
    (paperDesign_tauWorld _ _ _ _)
  refine { event := E ∩ optionBGood (paperDesignP 12225)
           measurable := hE.inter (optionBGood_measurable _)
           retained_charge := ?_
           frame_bound := ?_
           root_bound := ?_ }
  · have hs : H ∩ (E ∩ optionBGood (paperDesignP 12225))ᶜ ⊆
        (H ∩ Eᶜ) ∪ (optionBGood (paperDesignP 12225))ᶜ := by
      intro c hc
      by_cases he : c ∈ E
      · exact Or.inr (fun ht => hc.2 ⟨he, ht⟩)
      · exact Or.inl ⟨hc.1, he⟩
    exact (measureReal_mono hs (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add hcharge hTI))
  · intro c hc v
    obtain ⟨F⟩ := hframe c hc
    exact frame_from_inputs F hc.2.2 v
  · intro c hc
    obtain ⟨R⟩ := hroot c hc
    exact (BstLean.Part241.root_new_8000 (by omega) t c R.split R.window R.passes
      R.fluctuation).trans R.scalar

/-- The row uses the local covariance contract, with the World package and
the remaining charged frame and root inputs explicit. -/
theorem row_classifier_from_inputs
    {cell : Fin 60 → Set ℝ} {capTable : Fin 60 → ℝ}
    (W : WorldPackage (paperProgram 12225)
      (BstLean.Part243.rowWorldParameters BstLean.Part243.proposedHiddenCharge))
    (t : ℝ) {E : Set (Ret 12225)} (hE : MeasurableSet E)
    (hcharge : (retDist (paperCentres 12225)).real
      (BstLean.Part159.Hof W.hidden ∩ Eᶜ) ≤ baseChargeAllowance)
    (hframe : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ optionBGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius, Nonempty (LocalFrameInputs cell capTable c optionBAgentFrame))
    (hroot : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ optionBGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot)) :
    99 / 100 ≤ ((mlpTriple 2 12225).prod (sampMeas (10 ^ 12) 12225)).real
      {x | successNet x.1 t (progOut (paperDesignP 12225) t aL (10 ^ 12) x.1 x.2)} := by
  have A := agentPackage hE hcharge hframe hroot
  rw [base_charge_restored] at A
  exact BstLean.Part243.checked_junction (by norm_num) W t optionBScalarRow A le_rfl

end BstLean.Part253
