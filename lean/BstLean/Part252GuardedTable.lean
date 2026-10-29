import BstLean.Part252HQPackage

/-! Only table failures inside the paid analytic base enter its complement
payment. The remaining allowance retains all rational slack. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

noncomputable def guardedTableAllowance : ℝ :=
  BstLean.Part249.baseChargeAllowance - analyticCharge

theorem guarded_table_allocation :
    analyticCharge + guardedTableAllowance = BstLean.Part249.baseChargeAllowance := by
  unfold guardedTableAllowance
  ring

theorem guarded_table_allowance_exact :
    guardedTableAllowance = (1061112347681 / 10 ^ 15 : ℝ) := by
  norm_num [guardedTableAllowance, analyticCharge, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

theorem guarded_table_slack :
    guardedTableAllowance - tableChargeAllowance = (8357701297 / 10 ^ 15 : ℝ) := by
  rw [guarded_table_allowance_exact]
  norm_num [tableChargeAllowance]

structure GuardedTablePayment (H : Set (Ret 12225)) : Prop where
  charge : (retDist (paperCentres 12225)).real (H ∩ paidBaseEvent ∩ tableEventᶜ) ≤
    guardedTableAllowance

theorem guardedTablePayment_of_tablePayment {H : Set (Ret 12225)}
    (h : TablePayment H) : GuardedTablePayment H := by
  refine ⟨?_⟩
  have hs : H ∩ paidBaseEvent ∩ tableEventᶜ ⊆ H ∩ tableEventᶜ :=
    fun _ hc => ⟨hc.1.1, hc.2⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans h.charge).trans (by
    rw [guarded_table_allowance_exact]
    norm_num [tableChargeAllowance])

theorem hqBaseEvent_charge_of_guarded {H : Set (Ret 12225)}
    (h : GuardedTablePayment H) :
    (retDist (paperCentres 12225)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ (H ∩ paidBaseEvent ∩ tableEventᶜ) := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr ⟨⟨hc.1, hp⟩, fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge h.charge))).trans
      guarded_table_allocation.le

end BstLean.Part252
