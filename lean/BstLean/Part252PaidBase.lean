import BstLean.Part252BaseEvent
import BstLean.Part252PositiveOutput

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12225) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12225)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12225)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12225)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12225)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12225)

theorem paidBaseCertificate (H : Set (Ret 12225)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part252
