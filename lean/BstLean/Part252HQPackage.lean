import BstLean.Part252HQRoot
import BstLean.Part252SharedPackage
import BstLean.Part252PaidBase

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12225) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12225)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12225)} (h : TablePayment H) :
    (retDist (paperCentres 12225)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12225))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12225} (t : ℝ)
    (hw : WINDOW (paperDesignP 12225) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm

/-- This package has no root remainder or replacement conclusion premise. -/
noncomputable def hqAgentPackage_of_base_charge {H : Set (Ret 12225)}
    (hcharge : (retDist (paperCentres 12225)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance) (t : ℝ)
    (hframe : ∀ c ∈ goodSet H (hqBaseEvent ∩ sharedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame))
    (hmass : ∀ c ∈ goodSet H (hqBaseEvent ∩ sharedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius, LowResidualMass c) :
    BstLean.Part243.AgentPackage 12225 H BstLean.Part243.rowRadius
      BstLean.Part249.optionBAgentFrame BstLean.Part243.rowRoot
      BstLean.Part243.proposedRetainedCharge t := by
  refine { event := hqBaseEvent ∩ sharedGood (paperDesignP 12225)
           measurable := hqBaseEvent_measurable.inter (sharedGood_measurable _)
           retained_charge := ?_
           frame_bound := ?_
           root_bound := ?_ }
  · have hs : H ∩ (hqBaseEvent ∩ sharedGood (paperDesignP 12225))ᶜ ⊆
        (H ∩ hqBaseEventᶜ) ∪ (sharedGood (paperDesignP 12225))ᶜ := by
      intro c hc
      by_cases hb : c ∈ hqBaseEvent
      · exact Or.inr fun hg => hc.2 ⟨hb, hg⟩
      · exact Or.inl ⟨hc.1, hb⟩
    have hh := (measureReal_mono hs (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans
        (add_le_add hcharge
          (sharedGood_charge (by norm_num) (paperDesignP 12225)
            (paperDesign_tauWorld _ _ _ _))))
    simpa only [BstLean.Part249.base_charge_restored] using hh
  · intro c hc v
    obtain ⟨F⟩ := hframe c hc
    exact BstLean.Part249.frame_from_inputs (by norm_num) F
      (sharedGood_subset (by norm_num) _ hc.2.2) v
  · intro c hc
    obtain ⟨F⟩ := hframe c hc
    let R := hqRootInputs_on_base t (window_of_frame F) hc.2.1 (hmass c hc)
    exact (BstLean.Part241.root_new_8000 (by norm_num) t c R.split R.window
      R.passes R.fluctuation).trans R.scalar

/-- The original table-payment interface remains available. -/
noncomputable def hqAgentPackage {H : Set (Ret 12225)} (h : TablePayment H) (t : ℝ)
    (hframe : ∀ c ∈ goodSet H (hqBaseEvent ∩ sharedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame))
    (hmass : ∀ c ∈ goodSet H (hqBaseEvent ∩ sharedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius, LowResidualMass c) :
    BstLean.Part243.AgentPackage 12225 H BstLean.Part243.rowRadius
      BstLean.Part249.optionBAgentFrame BstLean.Part243.rowRoot
      BstLean.Part243.proposedRetainedCharge t :=
  hqAgentPackage_of_base_charge (hqBaseEvent_charge h) t hframe hmass

end BstLean.Part252
