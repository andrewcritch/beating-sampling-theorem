import BstLean.Part258Frame
import BstLean.Part257Root

/-! The World certificate supplies the exact selected window unconditionally. -/
namespace BstLean.Part258
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192 BstLean.Part196
open BstLean.Part169 (paperDesignP)
open BstLean.Part255 (parameters payment)
open BstLean.Part257 (sourceBase sourceBase_measurable sourceBase_allowance
  sourceEvents_of_base rootInputs_of_base)

noncomputable def commonEvent : Set (Ret 12225) :=
  sourceBase ∩ BstLean.Part256.covarianceGood (selected parameters payment)

theorem commonEvent_measurable : MeasurableSet commonEvent :=
  sourceBase_measurable.inter
    (BstLean.Part256.covarianceGood_measurable (selected_measurable _ _))

theorem selected_good_charge :
    (retDist (BstLean.Part157.paperCentres 12225)).real
      (BstLean.Part256.covarianceGood (selected parameters payment))ᶜ ≤
        (3/10000 : ℝ) :=
  BstLean.Part256.covarianceGood_charge paper_selected_payment

def SelectedWindowSupply : Prop :=
  ∀ c ∈ goodSet (BstLean.Part159.Hof BstLean.Part250.worldPackage.hidden)
    commonEvent (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius,
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      Icc worldLower worldUpper

theorem selectedWindowSupply : SelectedWindowSupply := by
  intro c hc
  have ha := hc.2.1.1.1.1
  have hang := BstLean.Part252.analyticBaseCertificate.angles ha
  exact BstLean.Part250.internalWorld.noise_window c ⟨hc.1.1, hang⟩

theorem commonEvent_charge (H : Set (Ret 12225)) :
    (retDist (BstLean.Part157.paperCentres 12225)).real (H ∩ commonEventᶜ) ≤
      (1799145/10^9 : ℝ) := by
  have hs : H ∩ commonEventᶜ ⊆
      (H ∩ sourceBaseᶜ) ∪
        (BstLean.Part256.covarianceGood (selected parameters payment))ᶜ := by
    intro c hc
    by_cases hb : c ∈ sourceBase
    · exact Or.inr (fun hg => hc.2 ⟨hb, hg⟩)
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (BstLean.Part257.sourceBase_charge H) selected_good_charge))).trans
        (by norm_num)

theorem classifier_12225 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12225).prod (sampMeas (10 ^ 12) 12225)).real
      {x | successNet x.1 t
        (progOut (paperDesignP 12225) t aL (10 ^ 12) x.1 x.2)} := by
  apply BstLean.Part256.row_classifier_from_inputs
    (cell := cell) (capTable := localCapTable) BstLean.Part250.worldPackage t
    (selected_measurable _ _) paper_selected_payment
    sourceBase_measurable (sourceBase_allowance _)
  · intro c hc
    obtain ⟨i, hi, hm⟩ := cells_cover (selectedWindowSupply c hc)
    exact ⟨selectedFrameInputs hi hm (sourceEvents_of_base hc.1.1 hc.2.1)⟩
  · intro c hc
    exact ⟨rootInputs_of_base t hc.1.1 hc.2.1⟩

end BstLean.Part258
