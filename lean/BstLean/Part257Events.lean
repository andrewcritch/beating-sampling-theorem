import BstLean.Part252CompletedRoot
import BstLean.Part256Common

/-! The source operator event fits the base allowance with the selected event. -/
namespace BstLean.Part257
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part161
open BstLean.Part169 (paperDesignP)
open BstLean.Part252

noncomputable def sourceBase : Set (Ret 12225) :=
  hqBaseEvent ∩ agentEv (paperDesignP 12225) (Operator160 12225)

theorem sourceBase_measurable : MeasurableSet sourceBase :=
  hqBaseEvent_measurable.inter (measurableSet_agentEv _ (measurableSet_Operator160 _))

theorem sourceBase_charge (H : Set (Ret 12225)) :
    (retDist (paperCentres 12225)).real (H ∩ sourceBaseᶜ) ≤ (1499145 / 10^9 : ℝ) := by
  have hs : H ∩ sourceBaseᶜ ⊆ (H ∩ hqBaseEventᶜ) ∪
      (agentEv (paperDesignP 12225) (Operator160 12225))ᶜ := by
    intro c hc
    by_cases hb : c ∈ hqBaseEvent
    · exact Or.inr (fun ho => hc.2 ⟨hb, ho⟩)
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (certified_hq_base_charge H)
      (operator160_ret_charge (by norm_num) (paperDesignP 12225)
        (paperDesign_tauWorld _ _ _ _))))).trans (by norm_num)

theorem sourceBase_allowance (H : Set (Ret 12225)) :
    (retDist (paperCentres 12225)).real (H ∩ sourceBaseᶜ) ≤
      BstLean.Part249.baseChargeAllowance :=
  (sourceBase_charge H).trans (by norm_num [BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge])

theorem sourceEvents_of_base {c : Ret 12225}
    (hw : c ∈ Hof BstLean.Part250.worldPackage.hidden) (hc : c ∈ sourceBase) :
    BstLean.Part253.SourceEvents c := by
  have ha := hc.1.1.1
  have hwin := actual_world_window hw ha
  have hsrc := analyticBaseCertificate.centre_sources ha hwin.2.1
  have hn : 0 < normSq c.1.2 :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm fun h => hwin.1 (normSq_eq_zero h))
  refine ⟨hn, hwin.2.1, ?_, ?_, ?_, ?_⟩
  · exact ⟨2, by norm_num, hsrc⟩
  · exact analyticBaseCertificate.direction ha hwin.2.1
  · have he : (6 / 1000 : ℝ) = 0.006 := by norm_num
    rw [← he]
    exact hc.2 hwin.2.1
  · exact (analyticBaseCertificate.pass_fields ha).1.1.1.1 hwin.2.1

noncomputable def commonEvent : Set (Ret 12225) :=
  sourceBase ∩ BstLean.Part255.selectedGood (paperDesignP 12225)

theorem commonEvent_measurable : MeasurableSet commonEvent :=
  sourceBase_measurable.inter
    (BstLean.Part256.covarianceGood_measurable (BstLean.Part255.selected_measurable _ _))

theorem commonEvent_charge (H : Set (Ret 12225)) :
    (retDist (paperCentres 12225)).real (H ∩ commonEventᶜ) ≤ (1799145 / 10^9 : ℝ) := by
  have hs : H ∩ commonEventᶜ ⊆ (H ∩ sourceBaseᶜ) ∪
      (BstLean.Part255.selectedGood (paperDesignP 12225))ᶜ := by
    intro c hc
    by_cases hb : c ∈ sourceBase
    · exact Or.inr (fun hg => hc.2 ⟨hb, hg⟩)
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (sourceBase_charge H)
      BstLean.Part255.paper_selected_good_charge))).trans (by norm_num)

theorem commonEvent_allowance (H : Set (Ret 12225)) :
    (retDist (paperCentres 12225)).real (H ∩ commonEventᶜ) ≤
      BstLean.Part243.proposedRetainedCharge :=
  (commonEvent_charge H).trans (by norm_num [BstLean.Part243.proposedRetainedCharge])

end BstLean.Part257
