import BstLean.Part262Events

/-! The selected covariance and moment event has one separate payment.
The base event pays Operator160 internally, as in Part257. -/
namespace BstLean.Part262
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part169

def commonEvent (n : ℕ) (covarianceEvent : Set (AgFam n)) : Set (Ret n) :=
  sourceBase n ∩ BstLean.Part259.covarianceGood covarianceEvent

theorem commonEvent_measurable {n : ℕ} (hn : 1 ≤ n)
    {covarianceEvent : Set (AgFam n)} (hE : MeasurableSet covarianceEvent) :
    MeasurableSet (commonEvent n covarianceEvent) :=
  (sourceBase_measurable hn).inter (BstLean.Part259.covarianceGood_measurable hE)

theorem commonEvent_charge {n : ℕ} (hn : 12225 ≤ n) {b : ℝ}
    {covarianceEvent : Set (AgFam n)}
    (hTable : (retDist (paperCentres n)).real (tableEvent n)ᶜ ≤ b)
    (hCovariance : (retDist (paperCentres n)).real
      (agentEv (paperDesignP n) covarianceEvent)ᶜ ≤ (1 / 4000 : ℝ))
    (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (commonEvent n covarianceEvent)ᶜ) ≤
      899145 / 10 ^ 9 + b := by
  have hs : H ∩ (commonEvent n covarianceEvent)ᶜ ⊆
      (H ∩ (sourceBase n)ᶜ) ∪
        (BstLean.Part259.covarianceGood covarianceEvent)ᶜ := by
    intro c hc
    by_cases hb : c ∈ sourceBase n
    · exact Or.inr (fun hg => hc.2 ⟨hb, hg⟩)
    · exact Or.inl ⟨hc.1, hb⟩
  have hp := BstLean.Part259.covarianceGood_charge (by omega) hCovariance
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (sourceBase_charge hn hTable H) hp))).trans (by linarith)

end BstLean.Part262
