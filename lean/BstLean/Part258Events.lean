import BstLean.Part258Supply

/-! The exact World cells retain one selected-event payment. -/
namespace BstLean.Part258
open MeasureTheory Real Set BstLean.Part255
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part150 (thetaC)

theorem clipped_supply (j : Fin 43) :
    Supply (parameters j) (cellLower (sourceIndex j)) (cellUpper (sourceIndex j)) := by
  have S := supplies j
  exact ⟨S.valid, S.wide_num, S.core_num,
    fun θ hθ => S.wide_guard θ (cell_source hθ),
    fun θ hθ => S.core_guard θ (cell_source hθ)⟩

noncomputable def selected (p : Fin 43 → Parameters) (ε : ℝ) : Set (AgFam 12225) :=
  BstLean.Part254.selectedEvent select (fun j => localEvent (p j)
    (cellLower (sourceIndex j)) (cellUpper (sourceIndex j)) ε)

theorem selected_measurable (p : Fin 43 → Parameters) (ε : ℝ) :
    MeasurableSet (selected p ε) :=
  BstLean.Part254.selectedEvent_measurable select select_measurable _
    (fun _ => localEvent_measurable _ _ _ _)

theorem selected_charge (p : Fin 43 → Parameters)
    (S : ∀ j, Supply (p j) (cellLower (sourceIndex j))
      (cellUpper (sourceIndex j)))
    (D : Design 12225) (hτW : TauWorld D) {ε : ℝ} (hε : 0 < ε) :
    (retDist D.toCentres).real (agentEv D (selected p ε))ᶜ ≤ ε := by
  exact BstLean.Part254.selectedEvent_ret_charge D hτW select select_measurable _
    (fun _ => localEvent_measurable _ _ _ _) hε.le
    (fun c τ hτ => localEvent_charge (S _) hε c hτ)


theorem selected_payment (D : Design 12225) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (selected parameters payment))ᶜ ≤
      (1/4000 : ℝ) :=
  selected_charge parameters clipped_supply D hτW (by norm_num [payment])

theorem paper_selected_payment :
    (retDist (BstLean.Part169.paperDesignP 12225).toCentres).real
      (agentEv (BstLean.Part169.paperDesignP 12225) (selected parameters payment))ᶜ ≤
        (1/4000 : ℝ) :=
  selected_payment _ (paperDesign_tauWorld _ _ _ _)

end BstLean.Part258
