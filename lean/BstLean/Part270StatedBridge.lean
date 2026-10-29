import BstLean.Part270Bridge
import BstLean.Part278Row

/-! Transfer the Part270 row families to the stated program without a new event charge. -/
namespace BstLean.Part270
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part169 BstLean.Part188
open BstLean.Part192 BstLean.Part196

theorem sourceBase_three_events {n : ℕ} {c : Ret n}
    (hc : c ∈ BstLean.Part262.sourceBase n) :
    c ∈ BstLean.Part160.agentEv (paperDesignP n) (BstLean.Part252.FirstMatrix n) ∧
    c ∈ BstLean.Part164.Eop2 n ∧
    c ∈ BstLean.Part252.outputCentreEvent (paperCentres n) :=
  ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩

theorem classifier_stated_of_source_family {S : Set ℕ}
    (R : BstLean.Part259.FamilyInputs S)
    (hdim : ∀ n ∈ S, 12000 ≤ n)
    (hbase : ∀ n (hn : n ∈ S), (R.row n hn).baseEvent = BstLean.Part262.sourceBase n) :
    ∀ n ∈ S, ∀ t : ℝ,
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t
        (progOut (BstLean.Part272.statedDesign n) t aL (10^12) x.1 x.2)} := by
  apply BstLean.Part278.classifier_on_set_st R
  intro n hn ho t
  apply BstLean.Part278.oddRoot_row (R.row n hn) (hdim n hn) ho t
  intro c hc
  rw [hbase n hn] at hc
  exact sourceBase_three_events hc

end BstLean.Part270
