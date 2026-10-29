import BstLean.Part262Common

/-! The paid analytic source event supplies all source memberships.
The exact-table event is a separate intersection and payment. -/
namespace BstLean.Part262
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169

theorem sourceEvents_of_paid {n : ℕ} {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (hc : c ∈ paidSourceBase n) : SourceEvents c := by
  have ha := hc.1.1
  have hn : 0 < normSq c.1.2 :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm fun h => hw.1 (normSq_eq_zero h))
  refine ⟨hn, hw.2.1, ?_, ?_, ?_, ?_⟩
  · exact ⟨2, by norm_num, ha.1.2 hw.2.1⟩
  · exact ha.1.1.2 hw.2.1
  · have he : (6 / 1000 : ℝ) = 0.006 := by norm_num
    rw [← he]
    exact hc.2 hw.2.1
  · exact ha.1.1.1.1.1.1.1 hw.2.1

structure ActualSourceSupply (n : ℕ) (charge : ℝ) where
  event : Set (Ret n)
  measurable : MeasurableSet event
  payment : ∀ H : Set (Ret n),
    (retDist (paperCentres n)).real (H ∩ eventᶜ) ≤ charge
  sources : ∀ c, WINDOW (paperDesignP n) c → c ∈ event → SourceEvents c

noncomputable def paidSourceSupply {n : ℕ} (hn : 12225 ≤ n) :
    ActualSourceSupply n (599145 / 10 ^ 9) where
  event := paidSourceBase n
  measurable := paidSourceBase_measurable (by omega)
  payment := paidSourceBase_charge hn
  sources := fun _ hw hc => sourceEvents_of_paid hw hc

end BstLean.Part262
